# Sage Imports
from sage.all import (
    Integer,
)

from sage.structure.element import Element, RingElement
from theta_structure import ThetaStructure, ThetaStructure_level2
from sage.structure.richcmp import richcmp_by_eq_and_lt

# ======================================== #
#     Class for Theta Point                #
# ======================================== #
# TODO rename _coords to _coordinates?
# TODO do we care about affine equality? 
#   if so, new class where we overwrite _eq
# TODO transform coordwise_invert into a method of the point, that saves the inverse coordinates in a tuple _inverses
#      or returns notimplementederror if we find a zero point
        

class ThetaPoint(Element):
    def __init__(self, parent, coords):
        # TODO support calling with several arguments?
        # TODO check validity of a theta point on a given parent? like is_x_coordinate on elliptic curves
        super().__init__(parent)

        if coords == 0:
            coords = parent.zero().coordinates()

        coords = tuple(coords)
        if not any(coords):
            raise ValueError("projective point cannot must have at least one nonzero coordinate")
        
        self._coords = coords
    
    def coordinates(self):
        """
        Return the projective coodinates of the ThetaPoint
        """
        return self._coords
    
    def _repr_(self):
        return f"{self.coordinates()}"

    def is_zero(self):
        """
        An element is zero if it is equivalent to the null point of the parent
        ThetaStrcuture
        """
        # TODO transform into a (not bool()) conversion as soon as we implement A(0) = A.zero()
        return self == self.parent().zero()
    
    def bool(self):
        return not self.is_zero()
    
    def scale(self, n):
        """
        Scale all coordinates of the ThetaPoint by `n`
        """
        if not isinstance(n, RingElement):
            # TODO how to check if multiplication between n and base_ring is well defined?
            raise ValueError(f"cannot scale by element {n} of type {type(n)}")
        if not n:
            raise ValueError(f"cannot scale projective coordinates by zero")
        
        scaled_coords = tuple(n * x for x in self.coordinates())
        return self._parent(scaled_coords)

    def __getitem__(self, n):
        return self.coordinates()[n]
    
    def __iter__(self):
        return iter(self.coordinates())
    
    def __len__(self):
        return len(self.coordinates())

    _richcmp_ = richcmp_by_eq_and_lt("_eq", "_lt")
    def _eq(self, other):
        """
        Check the quality of two ThetaPoints. Note that as this is a
        projective equality, we must be careful for when certain coefficients may
        be zero.
        """
        # TODO use ProjectiveSpace_point?
        if not isinstance(other, self.parent()._point):
            return NotImplemented
        if (self.parent().dimension(), self.parent().level()) != \
            (other.parent().dimension(), other.parent().level()):
            return NotImplemented

        zero_indices = (i for i in range(len(self)) if not self[i])
        if any(other[i] for i in zero_indices):
            return False
        
        nonzero_idx = next(i for i in range(len(self)) if self[i])
        return all(
            x * other[nonzero_idx] == y * self[nonzero_idx]
            for x, y in zip(self, other)
        )
    def _lt(self, other):
        return NotImplemented

class ThetaPoint_level2(ThetaPoint):
    """
    A Theta Point in the level-2 Theta Structure is defined with
    2**dimension projective coordinates

    We cannot perform arbitrary arithmetic, but we can compute doubles and
    differential addition, which like x-only points on the Kummer line, allows
    for scalar multiplication
    """

    # TODO what's the best way/place to put these static methods?
    @staticmethod
    def hadamard(*args, **kwds):
        return ThetaStructure_level2.hadamard(*args, **kwds)
    @staticmethod
    def square_coords(*args, **kwds):
        return ThetaStructure_level2.square_coords(*args, **kwds)
    @staticmethod
    def coordwise_multiply(*args, **kwds):
        return ThetaStructure_level2.coordwise_multiply(*args, **kwds)
    @staticmethod
    def coordwise_invert(*args, **kwds):
        # NOTE throws an error in case of division by 0
        return ThetaStructure_level2.coordwise_invert(*args, **kwds)
    
    # TODO move arithmetic_computation in a flag? it's already just two boolean checks, so probably 't's ok
    # TODO in this general formulation, double is really a special case of diff_add with no optimization. remove?
    def double(self):
        """
        Computes [2]*self

        Reference: https://eprint.iacr.org/2024/1180.pdf, Appendix A
        """
        self.parent()._arithmetic_precomputation()
        inv_0 = self.parent()._inv_null_point
        inv_U_sq = self.parent()._inv_null_point_dual_sq

        P = self.square_coords(self.hadamard(self.square_coords(self.coordinates())))
        # TODO is there a less cumbersome syntax? I'd like to just call hadamard and square_coords as functions;
        # I like them to be tied to the class instead of being global, but calling self.hadamard every time is also cumbersome...
        P = self.coordwise_multiply(P, inv_U_sq)
        P = self.hadamard(P)
        P = self.coordwise_multiply(P, inv_0)
        
        return self.parent()(P)
        
    def diff_addition(self, Q, PmQ, *, PmQ_is_inverse=False):
        """
        Given the theta points of P, Q and P-Q computes the theta point of
        P + Q.

        PmQ needs to be an iterable, not necessarily a point. TODO Do we like it?
        if PmQ_is_inverse, PmQ contains the inverse coordinates of P-Q
        otherwise, PmQ contains the coordinates of P-Q. The algorithm only uses the inverses.
        """
        self.parent()._arithmetic_precomputation()
        inv_U_sq = self.parent()._inv_null_point_dual_sq

        P = self.hadamard(self.square_coords(self.coordinates()))
        Q = self.hadamard(self.square_coords(Q.coordinates()))
        R = self.coordwise_multiply(P, Q)
        R = self.coordwise_multiply(R, inv_U_sq)

        PmQ = tuple(PmQ)
        if not PmQ_is_inverse:
            PmQ = self.coordwise_invert(PmQ, parent=self.parent())

        R = self.coordwise_multiply(R, PmQ)
        return R

    def __mul__(self, m):
        """
        Uses Montgomery ladder to compute [m] Self

        NOTE: Assumes that no coordinate is zero at any point during the doubling
        """
        # TODO how to deal with the NOTE above? assumption that no zero coordinate is encountered?...
        # TODO integrate .double(), .double_iter() here?
        # TODO distinguish whether we're level-2 (Kummer) or higher level (full group law)
        
        # Make sure we're multiplying by something value
        m = Integer(m)

        # If m is zero, return the null point
        if not m:
            return self.parent().zero()

        # We are with ±1 identified, so we take the absolute value of m
        m = abs(m)

        ##### NOTE just added by ale:
        # First perform a bulk of doublings, if possible.
        # If m = 2^n, then we skip the subsequent Montgomery ladder
        P0 = self
        for _ in range(m.valuation(2)):
            P0 = P0.double()
        m = m >> m.valuation(2)
        # TODO check ladder
        #############################
        
        # now m is odd
        if m == 1:
            return P0
        
        P1 = P0
        P2 = P1.double()
        P0inv = self.coordwise_invert(P0.coordinates(), parent=self.parent())

        # Montgomery double and add.
        for bit in bin(m)[3:]:
            Q = P2.diff_addition(P1, P0inv, PmQ_is_inverse=True)
            if bit == "1":
                P2 = P2.double()
                P1 = Q
            else:
                P1 = P1.double()
                P2 = Q

        return P1
    
    def __rmul__(self, m):
        # TODO do we still need rmul and imul with the sage type infrastructure?
        return self * m

    def __imul__(self, m):
        self = self * m
        return self
