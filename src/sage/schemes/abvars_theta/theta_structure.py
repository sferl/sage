# Sage Imports
from sage.all import (
    cached_method,
    Parent,
    UniqueRepresentation,
    ZZ
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
# TODO do we want to support batch inversion here in sage?
# TODO credits: some code adapted from Pierrick Dartois's 4dim library https://github.com/Pierrick-Dartois/Theta_dim4
#               main structure adapted from two-isogenies https://github.com/ThetaIsogenies/two-isogenies/tree/main/Theta-SageMath

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
        return super().__classcall__(*args, **kwds)

    def __init__(self, null_point, *, dimension=2, level=2):
        # TODO build a constructor that returns either a thing of level 2 or a thing of higher level
        if dimension not in (1, 2) or level != 2:
            raise NotImplementedError("theta structures for abelian varieties currently only supported in dimension <=2 and level 2")
        
        # TODO support calling with a point instead of just its coordinates?
        
        null_point = tuple(null_point)  # throw error if not meaningful iterable
        if len(null_point) != level**dimension:
            raise ValueError(f"null point should have {level**dimension} coordinates")
        self._level = ZZ(level)
        self._dimension = ZZ(dimension)

        self._base_ring = cm.common_parent(*(c.parent() for c in null_point))

        self._null_point = self._point(self, null_point)

    def dimension(self):
        return self._dimension
    
    def level(self):
        return self._level

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
    # TODO instead of an init in ThetaStructure, we'd actually need a constructor like EllipticCurve, right?
    # TODO is __init__ overridden like this correct? what about __classcall__ inheritance...?
    def __init__(self, null_point, *, dimension=1, level=2):
        if level != 2:
            raise ValueError("level must be 2")
        super().__init__(null_point, dimension=dimension, level=2)
        self._inv_null_point = None
        self._inv_null_point_dual_sq = None

    @staticmethod
    def hadamard(coords):
        coords = tuple(coords)

        def _hadamard_rec(coords_rec):
            if len(coords_rec) == 1:
                return coords_rec
            
            mid = len(coords_rec // 2)
            left = coords_rec[:mid]
            right = coords_rec[mid:]

            left = _hadamard_rec(left)
            right = _hadamard_rec(right)

            return tuple(x + y for x, y in zip(left, right)) + tuple(x - y for x, y in zip(left, right))
        
        return _hadamard_rec(coords)
    
    @staticmethod
    def coordwise_square(coords):
        # NOTE assumes coords is an iterable
        return tuple(x * x for x in coords)
    
    @staticmethod
    def coordwise_invert(coords, parent=None):
        # NOTE assumes coords is an iterable
        # NOTE parent just for debugging purposes
        if any(not x for x in coords):
            return NotImplementedError(f"division by zero as arithmetic on {parent} tried to invert point {coords}. Try applying manually a symplectic basis transformation")
        return tuple(1/x for x in coords)
    
    @staticmethod
    def coordwise_multiply(coords_1, coords_2):
        # NOTE assumes coords_i is an iterable of coordinates
        return tuple(x * y for x, y in zip(coords_1, coords_2))

    def arithmetic_precomputation(self):
        if self._inv_null_point is None:
            self._inv_null_point = self.coordwise_invert(self._null_point.coordinates(), parent=self)

        if self._inv_null_point_dual_sq is None:
            U_sq = self.hadamard(self.square_coords(self._null_point.coordinates()))
            self._inv_null_point_dual_sq = self.coordwise_invert(U_sq, parent=self)

    @staticmethod
    def hyperelliptic_curve_from_theta(J):
        """
        Convert a theta null point structure to an hyperelliptic curve
        """
        # TODO move to hyperelliptic curve class?
        from sage.all import HyperellipticCurve, PolynomialRing

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

        _, x = PolynomialRing(J.base_ring(), name="x").objgen()

        f_poly = x * (x - 1) * (x - lam) * (x - mu) * (x - nu)

        try:
            H = HyperellipticCurve(f_poly)
        except:
            raise ValueError("Converted curve is not a hyperelliptic curve")
        return H