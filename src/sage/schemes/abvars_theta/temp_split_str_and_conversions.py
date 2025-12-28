"""
NOTE this file is going to be obsolete. Class methods to be either integrated in EllipticProduct / ThetaStructure or deleted.
Keeping file here for now, to see what changes need to be done
and where to put these functions
"""
from sage.schemes.elliptic_curves.product import EllipticProduct
from sage.all import EllipticCurve

# Local imports
from theta_point import ThetaPoint
from theta_structure import ThetaStructure

# TODO where do we check that the structure is split?
#       is_split method in EllipticProduct?
#       is_split internal flag in the theta structure? split isomorphism (e.g. EllipticProduct <-> ThetaStructure that satisfies is_split())?
#       or is it actually good to have these product / split classes? 

class ProductThetaStructure(ThetaStructure):
    """
    Special case of a ThetaStructure, which is computed from two elliptic curves
    E1, E2 interpreted as a product: A = E1 x E2.

    The bulk of the work here is the mapping from the dimension one structure to
    the product dimension two structure. Bulk of the conversions come from

        Models of Kummer lines and Galois representation,
        Razvan Barbulescu, Damien Robert and Nicolas Sarkis
    """

    def __init__(self, E1, E2, B1=None, B2=None):
        # TODO transform into a method EllipticProduct.to_theta
        if B1 == None or B2 == None:
            # null point is dim 2 product
            # O01, O02 are the dim 1 null points
            null_point, O01, O02 = self.montgomery_curves_to_theta_null_point(E1, E2)

            self.E1 = E1
            self.E2 = E2

            self.O01 = O01
            self.O02 = O02

            ThetaStructure.__init__(self, null_point)
        else:
            self.E1 = E1
            self.E2 = E2

            self.O01 = montgomery_torsion_to_theta_null_point(B1[0])
            self.O02 = montgomery_torsion_to_theta_null_point(B2[0])

            null_point = self.pairwise_product(self.O01, self.O02)

            ThetaStructure.__init__(self, null_point)

    def __call__(self, *args):
        """
        Create a theta point on the product from either a pair of
        points, a CouplePoint or coefficients of a theta point.
        """
        P1, P2 = args # or EllipticProductPoint P.components()
        coords = self.montgomery_points_to_theta_point(P1, P2)
        return self._point(self, coords)


        return self._point(self, *args)

    def __repr__(self):
        # TODO delete
        return f"Product theta structure over {self.base_ring()} with null point: {self.null_point()}"

    def pairwise_product(self, O1, O2):
        """
        Given two dim-1 theta points, compute the level two theta point on the
        product.

        NOTE: The order used is implicitly 00, 10, 01, 11
        """
        # NOTE this is the Segre embedding
        # TODO use as small helper function or delete
        a1, b1 = O1
        a2, b2 = O2

        return (a1 * a2, b1 * a2, a1 * b2, b1 * b2)

    def montgomery_curves_to_theta_null_point(self, E1, E2):
        """
        Given a pair of elliptic curves, compute the corresponding
        dim-1 theta points as well as the coordinates of the
        level-2 null point.
        """
        # TODO move conversion to EllipticProduct. or transform the _init_ above to a morphism(/isomorphism?) so that it can be applied to points
        O1 = montgomery_curve_to_theta_null_point(E1)
        O2 = montgomery_curve_to_theta_null_point(E2)

        null_coords = self.pairwise_product(O1, O2)

        return null_coords, O1, O2

    def montgomery_points_to_theta_point(self, P1, P2):
        """
        Given two points P1, P2 on curves E1, E2 where it is
        assumed we have computed the corresponding dim-1
        theta null points, compute the product theta point
        from P1 x P2.
        """
        # TODO move conversion to EllipticProductPoint, or see NOTE in montgomery_curves_to_theta_null_point
        O1 = montgomery_point_to_theta_point(self.O01, P1)
        O2 = montgomery_point_to_theta_point(self.O02, P2)

        return self.pairwise_product(O1, O2)
    

class SplitThetaStructure:
    """
    Given some ThetaStructure which is isomorphic to a product of elliptic
    curves E1 x E2, this class takes as input a ThetaStructure and returns a new
    ThetaStrcuture which has a compatible representation: the dual, squared
    coordinate is in the index position (11, 11). In this form, computing the
    dimension one theta points (a : b) from (X : Y : Z : W) is simply a case of
    selecting the splitting (X : Y) and (Y : W)

    Contains helper functions which return the elliptic products E1 and E2 and also
    allows the mapping of some ThetaPoint P on A to the Elliptic Product E1 x E2.
    """

    def __init__(self, T):
        # TODO see TODOS at the beginning of the file
        if not isinstance(T, ThetaStructure):
            raise TypeError

        # Create dim 1 theta structures
        self.O1, self.O2 = self.split(T)

        # Compute Mont. curves
        self.E1 = theta_null_point_to_montgomery_curve(self.O1)
        self.E2 = theta_null_point_to_montgomery_curve(self.O2)

    def curves(self):
        """
        Returns the elliptic curves E1 and E2 in the Montgomery model using the
        formula of

            Models of Kummer lines and Galois representation,
            Razvan Barbulescu, Damien Robert and Nicolas Sarkis
        """
        # 
        return self.E1, self.E2

    @staticmethod
    def split(P):
        """
        Assuming the zero index of the ThetaStructure is in the (11, 11)
        postion, we can always obtain the dim-1 theta structure in the following
        way

        P = (a : b : c : d)

        P1 = (a : b)
        P2 = (b : d)

        This is because the product structure of P1 and P2 is simply:

        P = (a * b : b * b : a * b : b * d)

        And we see up to an overall scale factor we recover the projective
        factors essentially for free
        """
        # NOTE inverse of Segre embedding
        # NOTE dim-2 specific
        # TODO small helper function, or integrate somewhere?

        a, b, _, d = P.coords()

        P1 = (a, b)
        P2 = (b, d)

        return P1, P2

    @staticmethod
    def to_points(E, X, Z):
        """
        Given the (X : Z) point on the KummerLine of E compute the point
            ±P = (X : Y : Z) on the curve
        """
        # TODO this is just E.lift_x(X/Z). For a generic sage implementation, we can forget this method
        if Z == 0:
            return E(0)

        x = X / Z

        A = E.a_invariants()[1]
        y2 = x * (x**2 + A * x + 1)
        y = y2.sqrt()

        return E(x, y)

    def __call__(self, P, lift=True):
        """ """
        if not isinstance(P, ThetaPoint):
            raise TypeError

        # Dim 2 -> Dim 1 theta points
        P1, P2 = self.split(P)

        # Convert to Montgomery points
        Q1X, Q1Z = theta_point_to_montgomery_point(self.O1, P1)
        Q2X, Q2Z = theta_point_to_montgomery_point(self.O2, P2)

        if lift:
            # lift from the Kummer to the elliptic curve
            Q1 = self.to_points(self.E1, Q1X, Q1Z)
            Q2 = self.to_points(self.E2, Q2X, Q2Z)

            return EllipticProduct(self.E1, self.E2)(Q1, Q2)
        else:
            return [(Q1X, Q1Z), (Q2X, Q2Z)]


############################################################
### Theta <-> Montgomery conversions
############################################################

from collections import namedtuple

ThetaNullPoint = namedtuple("ThetaNullPoint_dim_1", "a b")

def theta_null_point_to_montgomery_curve(O0):
    """
    Given a level 2 theta null point (a:b), compute a Montgomery curve equation.
    We use the model where the 4-torsion point (1:0) above (a:-b) is sent to
    (1:1) in Montgomery coordinates.

    Algorithm from:
        Models of Kummer lines and Galois representation,
        Razvan Barbulescu, Damien Robert and Nicolas Sarkis
    """
    a, b = O0

    aa = a**2
    bb = b**2

    T1 = aa + bb
    T2 = aa - bb

    # Montgomery coefficient
    A = -(T1**2 + T2**2) / (T1 * T2)

    # Construct curve
    F = a.parent()
    E = EllipticCurve(F, [0, A, 0, 1, 0])
    return E


def montgomery_curve_to_theta_null_point(E):
    """
    From an elliptic curve in Montgomery form, compute a theta null point
    (a:b).
    Let T1=(1:1) the canonical point of 4-torsion in Montgomery coordinates
    and T2 such that (T1,T2) forms a symplectic basis of E[4].
    There are 4 choices of T2, giving 4 different theta null points.

    Algorithm from:
        Models of Kummer lines and Galois representation,
        Razvan Barbulescu, Damien Robert and Nicolas Sarkis
    """
    # TODO implement from generic curve shape? or implement intermediate conversion to montgomery?

    # Extract A from curve equation
    A = E.montgomery_model().a2()

    # alpha is a root of
    # x^2 + Ax + 1
    disc = A * A - 4
    assert disc.is_square()

    d = (A * A - 4).sqrt()
    alpha = (-A + d) / 2

    # The theta coordinates a^2 and b^2
    # are related to alpha
    aa = alpha + 1
    bb = alpha - 1

    aabb = aa * bb
    ab = aabb.sqrt()

    # We aren't given (a,b) rational, but
    # (a/b) is rational so we use
    # (ab : b^2) as the theta null point
    O0 = ThetaNullPoint(ab, bb)
    return O0


def montgomery_torsion_to_theta_null_point(P):
    """
    From a four torsion point T2 on a Montgomery curve, such that
    (T1,T2) is a symplectic basis of E[4] and T1=(1:1),
    compute the corresponding theta null point.

    Algorithm from:
        Models of Kummer lines and Galois representation,
        Razvan Barbulescu, Damien Robert and Nicolas Sarkis
    """
    r = P[0]
    s = P[2]
    O0 = ThetaNullPoint(r + s, r - s)
    return O0


def theta_point_to_montgomery_point(O0, O):
    """
    Given an elliptic curve in Montgomery form
       E : y^2 = x^3 + Ax^2 + x
    and the theta null point with coordinates
       O0 = (a, b)

    Converts a theta point O = (U : V) on θ_(a,b)
    to a point P = (X : Z) on E

    Algorithm from:
        Models of Kummer lines and Galois representation,
        Razvan Barbulescu, Damien Robert and Nicolas Sarkis
    """
    a, b = O0
    U, V = O
    X = a * V + b * U
    Z = a * V - b * U

    return (X, Z)


def montgomery_point_to_theta_point(O0, P):
    """
    Given an elliptic curve in Montgomery form
       E : y^2 = x^3 + Ax^2 + x
    and the theta null point with coordinates
       (a, b)

    Converts a point P = (X : Z) on E to a point
    O = (U : V) on θ_(a,b)

    Algorithm from:
        Models of Kummer lines and Galois representation,
        Razvan Barbulescu, Damien Robert and Nicolas Sarkis
    """
    if P.is_zero():
        return O0[:]

    a, b = O0
    X, Z = P[0], P[2]
    if X == Z and Z == 0:  # Do not forget the origin
        return (a, b)
    else:
        U = a * (X - Z)
        V = b * (X + Z)
        return (U, V)
