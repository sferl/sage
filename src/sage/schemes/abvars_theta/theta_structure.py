# Sage Imports
from sage.all import (
    cached_method,
    Integer,
    HyperellipticCurve,
    PolynomialRing,
    Parent,
    UniqueRepresentation
)

from sage.structure.element import get_coercion_model, RingElement
cm = get_coercion_model()
from theta_point import ThetaPoint

# ============================================ #
#     Class for Theta Structure (level-2?)     #
# ============================================ #

# TODO a Kummer variety (level 2) has no group arithmetic --> diff_add and double() instead of just _add_
# How to put into classes? Kummer vs regular theta work differently
# TODO projective points, projective equality&arithmetic vs affine(cubical) ? what do we do
# TODO important: add support for dimension-1 theta structures for Elliptic curves / Kummer lines

class ThetaStructure(Parent, UniqueRepresentation):
    """
    Class for the ThetaStructure, defined by its theta null point.
    TODO references.
    """
    # TODO rename into Theta_Abelian_Variety or something?
    _point = ThetaPoint
    _element_constructor_ = _point

    @classmethod
    def __classcall__(cls, *args, **kwds):
        r"""
        Construct a theta structure of a given dimension and level from its
        null point (the coordinates of the additive identity).

        Method used for compatibility with UniqueRepresentation.
        """
        return super().__classcall__(cls, *args, **kwds)

    def __init__(self, null_point, *, dimension=2, level=2):
        if dimension not in (1, 2) or level != 2:
            raise NotImplementedError("theta structures for abelian varieties currently only supported in dimension <=2 and level 2")
        
        # TODO support calling with a point instead of just its coordinates?
        
        null_point = tuple(null_point)  # throw error if not meaningful iterable
        if len(null_point) != level**dimension:
            raise ValueError(f"null point should have {level**dimension} coordinates")

        self._base_ring = cm.common_parent(*(c.parent() for c in null_point))

        self._null_point = self._point(self, null_point)

    def zero(self):
        """
        Return the null point of the given theta structure
        """
        return self._null_point

    null_point = zero  # TODO keep alias?

    def base_ring(self):
        """
        Return the base ring of the common parent of the coordinates of the null point
        """
        return self._base_ring

    def __repr__(self):
        return f"Theta structure over {self.base_ring()} with null point: {self.null_point()}"

class ThetaStructure_level2(ThetaStructure):
    # TODO rename to Kummer? ThetaSurface? ...
    # TODO are there actually any specific methods? if the only specific methods are in the points, still keep it?
    # TODO instead of an init in ThetaStructure, we'd actually need a constructor like EllipticCurve, right?
    
    #####################################################
    ### dim-2 specific methods
    #####################################################
    
    def hadamard(self):
        # TODO keep?
        # NOTE dim-2^n specific
        """
        Compute the Hadamard transformation of the theta null point of the theta structure
        """
        return self.null_point().hadamard()

    def squared_theta(self):
        # NOTE dim-2^n specific
        # TODO generalize to twisted U_ii,ii coords
        """
        Square the coefficients and then compute the Hadamard transformation of
        the theta null point of the theta structure
        """
        return self.null_point().squared_theta()

    @staticmethod
    def hyperelliptic_curve_from_theta(J):
        """
        Convert a theta null point structure to an hyperelliptic curve
        """
        # TODO move to hyperelliptic curve class?
        if not isinstance(J, ThetaStructure):
            raise TypeError("J must be a 2-dimensional theta structure")
        if J.dimension() != 2:
            raise ValueError("theta structure must be of dimension 2")
        if J.level != 2:
            raise NotImplementedError("conversion to hyperelliptic curve only available from non-split dim-2 theta structures of level 2")
        
        # TODO check if split, only keep going if not
        #############################

        # Extract out the hadamard transform from the point class
        to_hadamard = J.zero().to_hadamard

        a, b, c, d = J.coords()
        A, C, B, D = to_hadamard(a, d, b, c)  # beware the weird order
        if A * B * C * D == 0:
            a, b, c, d = to_hadamard(a, b, c, d)
            A, C, B, D = to_hadamard(a, d, b, c)

        try:
            al = a * a + b * b + c * c + d * d
            be = 2 * (a * d + b * c)
            ga = 2 * (a * b + c * d)
            de = 2 * (a * c + b * d)
            CD_AB = C * D / (A * B)
            ep_phi = (1 + CD_AB) / (1 - CD_AB)
            lam = al * ga / (de * be)
            mu = ga / de * ep_phi
            nu = al / be * ep_phi

        except Exception as e:
            raise ValueError(f"Conversion to rosenhain failed because of: {e}")

        R = PolynomialRing(J.base_ring(), name="x")
        x = R.gens()[0]

        f_poly = x * (x - 1) * (x - lam) * (x - mu) * (x - nu)

        try:
            H = HyperellipticCurve(f_poly)
        except:
            raise ValueError("Converted curve is not a hyperelliptic curve")
        return H