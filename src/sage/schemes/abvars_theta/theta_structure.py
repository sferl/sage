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

    def __init__(self, null_point, *, dimension=2, level=2):
        # TODO set classcall, parent, element ... as with elliptic curves
        if dimension != 2 or level != 2:
            raise NotImplementedError("theta structures for abelian varieties currently only supported in dimension 2 and level 2")
        
        if len(null_point) != level**dimension:
            raise ValueError("null point does not have correct ")

        self._base_ring = cm.common_parent(*(c.parent() for c in null_point))
        self._point = ThetaPoint
        self._precomputation = None
        # TODO save precomputation in an easier way?

        self._null_point = self._point(self, null_point)

    def __call__(self, coords):
        # TODO re-factor with classcall ??
        # TODO support call with 0
        return self._point(self, coords)

    def null_point(self):
        """
        Return the null point of the given theta structure
        """
        return self._null_point
    
    zero = null_point  # the additive identity is the null point

    def base_ring(self):
        """
        Return the base ring of the common parent of the coordinates of the null point
        """
        return self._base_ring

    def __repr__(self):
        return f"Theta structure over {self.base_ring()} with null point: {self.null_point()}"

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

    # def _arithmetic_precomputation(self):
    #     """
    #     Precompute 6 field elements used in arithmetic and isogeny computations
    #     """
    #     if self._precomputation is None:
    #         a, b, c, d = self.null_point().coords()

    #         # Technically this computes 4A^2, 4B^2, ...
    #         # but as we take quotients this doesnt matter
    #         # Cost: 4S
    #         AA, BB, CC, DD = self.squared_theta()

    #         # Precomputed constants for addition and doubling
    #         b_inv, c_inv, d_inv, BB_inv, CC_inv, DD_inv = map(
    #             lambda x: x^(-1),
    #             (b, c, d, BB, CC, DD)
    #         )

    #         y0 = a * b_inv
    #         z0 = a * c_inv
    #         t0 = a * d_inv

    #         Y0 = AA * BB_inv
    #         Z0 = AA * CC_inv
    #         T0 = AA * DD_inv

    #         self._precomputation = (y0, z0, t0, Y0, Z0, T0)
    #     return self._precomputation

    @cached_method
    def rosenhain_from_theta(self):
        """
        From a theta null point structure, return the Rosenhain invariants
        """
        # TODO check if split, keep going if not
        # TODO dim-2 specific

        # Extract out the hadamard transform from the point class
        to_hadamard = self.zero().to_hadamard

        a, b, c, d = self.coords()
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

        return lam, mu, nu

    @cached_method
    def hyperelliptic_from_theta(self):
        """
        Convert a theta null point structure to an hyperelliptic curve
        """
        # TODO check if split, keep going if not
        # TODO dim-2 specific

        # Extract out the hadamard transform from the point class
        lam, mu, nu = self.rosenhain_from_theta()
        if lam is None:
            raise ValueError("Could not compute Rosenhain roots from the null point")

        R = PolynomialRing(self.base_ring(), name="x")
        x = R.gens()[0]

        f_poly = x * (x - 1) * (x - lam) * (x - mu) * (x - nu)

        try:
            H = HyperellipticCurve(f_poly)
        except:
            raise ValueError("Converted curve is not a hyperelliptic curve")
        return H