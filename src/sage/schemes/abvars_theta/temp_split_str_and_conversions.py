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
