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

# TODO projective points, projective equality&arithmetic vs affine(cubical) ? what do we do
# TODO do we want to support batch inversion here in sage?
# TODO credits: some code adapted from Pierrick Dartois's 4dim library https://github.com/Pierrick-Dartois/Theta_dim4
#               main structure adapted from two-isogenies https://github.com/ThetaIsogenies/two-isogenies/tree/main/Theta-SageMath
# TODO create a product-of-theta-structure class
# TODO type change of model (ell curve or kummer line into theta) as Morphism
# TODO have classes for a kummer line?


class ThetaStructure(Parent, UniqueRepresentation):
    """
    Class for the ThetaStructure, defined by its theta null point.
    TODO references.
    """
    # TODO rename into Theta_Abelian_Variety or something?
    _point = ThetaPoint
    _element_constructor_ = _point

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
    
    @classmethod
    def from_factors(cls, factors, *, with_morphism=False):
        # TODO support factors as multiple parameters
        # TODO make sure it makes sense as class method
        #       example: affine theta structure from factors should return an affine theta structure,
        #                or kummer variety should return kummer variety
        #      NOTE for that, we need that the __classcall__ or __init__ methods have compatible interface
        # TODO check python closures. for sure there will be some crazy bug going on there
        if any(not isinstance(factor, ThetaStructure) or factor.level() != factors[0].level()
               for factor in factors):
            raise TypeError("factors must be theta structures of the same level")
        dim = sum(factor.dimension() for factor in factors)
        lev = factors[0].level()

        null_points = tuple(factor.null_point() for factor in factors)

        def segre(points):
            # NOTE assumes points is a tuple
            import itertools
            from sage.all import prod    
            
            # one-liner for the Segre embedding, in the same ordering used by two-isogenies
            ret = tuple(prod(combination) for combination in itertools.product(*(points[::-1])))
            return ret
        
        null_point = segre(null_points)
        thetastr = cls(null_point, dimension=dim, level=lev)
        
        if not with_morphism:
            return thetastr
        else:
            # TODO morphism as function
            def _morphism(points):
                # TODO coercion then coordinate extraction does the necessary checks but might be inefficient;
                #      transform in simple check?
                points_coords = tuple(factor(point).coordinates() for factor, point in zip(factors, points))
                return thetastr(segre(points_coords))
            return thetastr, _morphism

    def is_split(self):
        raise NotImplementedError("check only available for dim-2 level-2 theta structures")

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
    
    # TODO put these funs out of the class
    @staticmethod
    def coordwise_square(coords):
        # NOTE assumes coords is an iterable
        return tuple(x * x for x in coords)
    
    @staticmethod
    def coordwise_invert(coords, parent=None):
        # NOTE assumes coords is an iterable
        # NOTE parent just for debugging purposes
        if any(not x for x in coords):
            raise NotImplementedError(f"division by zero as arithmetic on {parent} tried to invert point {coords}. Try applying manually a symplectic basis transformation")
        return tuple(~x for x in coords)
    
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

    # TODO move the following two methods to class ThetaStructure?
    # interface ThetaStructure.from_curve sounds prettier than with _level2 (but maybe too general?)
    @staticmethod
    def from_curve(curve, with_morphism=False):
        A = curve.montgomery_model().a2()
        
        # alpha is a root of x^2 + Ax + 1
        try:
            from sage.all import PolynomialRing
            _, x = PolynomialRing(A.parent(), name="x").objgen()
            alpha = (x**2 + A*x + 1).any_root()
        except ValueError:
            # TODO really catch this error? or let it slip in the root finding?
            raise ValueError("cannot convert Montgomery model to theta")

        # The theta coordinates a^2 and b^2 are related to alpha
        aa = alpha + 1
        bb = alpha - 1

        ab = (aa * bb).sqrt()
        # We aren't given (a,b) rational, but
        # (a/b) is rational so we use
        # (ab : b^2) as the theta null point
        null_point = (ab, bb)
        thetastr = ThetaStructure_level2(null_point, dimension=1)
        
        if not with_morphism:
            return thetastr
        else:
            def _morphism(point, *, domain_is_x_only=False):
                # TODO compose with the iso from given curve to montgomery...
                if not domain_is_x_only:
                    if point.is_zero():
                        point = (curve.base_ring()(1), curve.base_ring()(0))
                    else:
                        point = (curve(point)[0], curve(point)[2])
                
                a, b = null_point
                X, Z = tuple(point)
                if not curve.is_x_coord(X/Z):
                    raise ValueError("given x, z coordinates must lie on given curve")
                
                return thetastr((a * (X - Z), b * (X + Z)))
                
            return thetastr, _morphism

    # TODO replace curves with EllipticProduct!!!
    # TODO create a product-of-theta-structures class? would make sense with the morphisms and for consistency with elliptic product;
    #       its main functionality would be handling gluing and splitting
    @classmethod
    def from_curves(cls, curves, with_morphism=False):
        # TODO support curves as multiple parameters
        # TODO I'm afraid closures will make a mess. What's the correct interface for these changes of model?
        from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
        if any(not isinstance(curve, EllipticCurve_generic) for curve in curves):
            raise TypeError("factors should be instances of an elliptic curve class")

        if not with_morphism:
            factors = tuple(ThetaStructure_level2.from_curve(curve) for curve in curves)
            return cls.from_factors(factors)
        else:
            factors, curve_to_theta_morphisms = (zip(*(
                cls.from_curve(curve, with_morphism=True)
                for curve in curves
            )))
            thetastr, factors_to_prod = cls.from_factors(factors, with_morphism=True)

            def _morphism(points, *, domain_is_x_only=False):
                # TODO coercion then coordinate extraction does the necessary checks but might be inefficient;
                #      transform in simple check?
                theta_points = tuple(
                    curve_to_theta(curve, point, domain_is_x_only=domain_is_x_only)
                    for curve, point, curve_to_theta in zip(curves, points, curve_to_theta_morphisms)
                )
                return factors_to_prod(theta_points)
            
            return thetastr, _morphism
        
    def _level_22_constants_sqr(self, i, j):
        # TODO make it a vector instead of a function of i, j?
        """
        U_i,j
        https://eprint.iacr.org/2023/1747.pdf page 17, NOTE the formula is only true for P=0
        https://sferl.github.io/files/pdf_master_thesis.pdf formula (3.6) is correct TODO search reference in Damien's thesis
        """
        character = bin(i & j)[2:].count('1') % 2  # scalar product between bin(i) and bin(j)
        ret = sum(
            (-1)**character * self._null_point[t] * self._null_point[t ^ j]
            for t in range(2 ** self.dimension())
        )
        return ret

    def is_split(self):
        """
        https://eprint.iacr.org/2023/1747.pdf page 17, Dupont's thesis as a big reference
        """
        return any(not self._level_22_constants_sqr(i, j)
                   for i in range(2 ** self.dimension())
                   for j in range(2 ** self.dimension())
                   if bin(i & j)[2:].count('1') % 2 == 0)
    
    def split_into_theta_factors(self, with_morphism=False):
        if self.dimension() != 2:
            raise NotImplementedError("splitting only available in dimension 2")
        if not self.is_split():
            raise ValueError("given theta structure is not isomorphic to a product of elliptic curves")
        
        split_idx = next(
            (i, j)
            for i in range(2 ** self.dimension())
            for j in range(2 ** self.dimension())
            if bin(i & j)[2:].count('1') % 2 == 0 and self._level_22_constants_sqr(i, j) == 0
        )
        # TODO apply change of basis, to make sure split_idx == (3, 3)
        if split_idx != (3, 3):
            raise NotImplementedError("symplectic change of basis not implemented yet")
        
        def inv_segre(coords):
            # TODO generalize to higher dimension
            a, b, _, d = coords
            return (a, b), (b, d)
        
        theta_curves_null_points = inv_segre(self._null_point)
        theta_curves = tuple(ThetaStructure_level2(np, dimension=1) for np in theta_curves_null_points)

        if not with_morphism:
            return theta_curves
        else:
            def _morphism(coords):
                split_points = inv_segre(coords)
                return tuple(curve(point) for curve, point in zip(theta_curves, split_points))
            
            return theta_curves, _morphism
        
    def to_elliptic(self, with_morphism=False):
        # TODO rename to to_elliptic_curve?
        if self.dimension() != 1:
            raise TypeError("given theta structure must be of dimension 1")
        
        from sage.all import EllipticCurve
        
        a, b = self._null_point

        aa = a**2
        bb = b**2

        T1 = aa + bb
        T2 = aa - bb

        # Montgomery coefficient
        A = -(T1**2 + T2**2) / (T1 * T2)

        # Construct curve
        F = a.parent()
        E = EllipticCurve(F, [0, A, 0, 1, 0])

        if not with_morphism:
            return E
        else:
            def _morphism(coords, x_only=True):
                a, b = self._null_point  # FIXME redundant line, re-written here for better debugging
                U, V = coords
                X = a*V + b*U
                Z = a*V - b*U

                # TODO remove assertion
                assert E.is_x_coord(X/Z)
                
                if x_only:
                    return X, Z
                else:
                    return E.lift_x(X/Z)

        return E, _morphism

    to_montgomery = to_elliptic
        
    def split_into_curves(self, with_morphism=False):
        from sage.schemes.elliptic_curves.product import EllipticProduct
        if not with_morphism:
            factors = self.split_into_theta_factors(with_morphism=False)
            # FIXME what's wrong with the compiler here? says types are not correct
            curves = tuple(factor.to_elliptic() for factor in factors) # type: ignore    
            return EllipticProduct(curves)
        
        else:
            factors, prod_to_factors = self.split_into_theta_factors(with_morphism=True)
            curves, theta_to_curve_morphisms = (zip(*(
                factor.to_elliptic(with_morphism=True)
                for factor in factors
            )))
            ell_prod = EllipticProduct(curves)
            
            def _morphism(coords, x_only=True):
                split_theta_points = prod_to_factors(coords)
                ell_points = tuple(morphism(point, x_only=x_only)
                                   for morphism, point in zip(theta_to_curve_morphisms, split_theta_points))
                if x_only:
                    return ell_points  # a tuple of (X, Z) coordinates
                else:
                    return ell_prod(ell_points)  # EllipticProductPoint
            
            return ell_prod, _morphism

    @staticmethod
    def hyperelliptic_curve_from_theta(J):
        """
        Convert a theta null point structure to an hyperelliptic curve
        """
        # TODO move to hyperelliptic curve class?
        from sage.all import HyperellipticCurve, PolynomialRing

        if not isinstance(J, ThetaStructure):
            raise TypeError("J must be a theta structure")
        if J.dimension() != 2:
            raise NotImplementedError("theta structure must be of dimension 2")
        if J.is_split():
            raise ValueError("given theta structure is not isomorphic to a hyperelliptic Jacobian")
        if J.level != 2:
            raise NotImplementedError("conversion to hyperelliptic curve only available from theta structures of level 2")
        
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
    
    # TODO from_hyperelliptic