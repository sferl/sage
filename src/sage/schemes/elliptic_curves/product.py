r"""
Products of elliptic curves

Given `n` elliptic curves `E_1, \dots, E_n` over a ring `R`,
their product `E_1 \times \dots \times E_n` is a principally polarized
abelian variety of dimension `n`.

This module defines a parent class :class:`EllipticProduct` to provide support
for such products, and an element class :class:`EllipticProductPoint` to
represent points on them, which are of the form
`(P_1, \dots, P_n) \in E_1 \times \dots \times E_n`.

EXAMPLES::

    sage: Fp2.<i> = GF(419^2, modulus=[1,0,1])
    sage: E0, E1 = EllipticCurve(Fp2, [1,0]), EllipticCurve(Fp2, [3,4])
    sage: E0E1 = EllipticProduct(E0, E1); E0E1
    Product of elliptic curves: (Elliptic Curve defined by y^2 = x^3 + x over Finite Field in i of size 419^2, Elliptic Curve defined by y^2 = x^3 + 3*x + 4 over Finite Field in i of size 419^2)
    sage: P0, P1 = E0.lift_x(-1), E1([5, 12])
    sage: P0P1 = E0E1(P0, P1)
    sage: all(P in E for P, E in zip(P0P1, E0E1.factors()))
    True

.. TODO::

    Implement isogenies between products of elliptic curves:: 

        sage: P0, Q0 = E0.torsion_basis(4)
        sage: prod = EllipticProduct(E0, E0)
        sage: prod.isogeny([prod(P0, P0), prod(Q0, Q0)])  # not implemented

AUTHORS:

- Alessandro Sferlazza (2025): Initial version
"""

# TODO:
# - nicer error messages?
# - setup all the #needs
# - instead of making EllipticProduct a globally available name, we could add a .product() method in EllipticCurves ???
#   and only allow syntax like E.product(E').
#   This way, this way of building arbitrary products: curves=..., EllipticProduct(curves)   wouldn't be allowed
# - __init__ assumes that the curves were already unpacked in __classcall__. Leave __classcall__ generic with *args, **kwds and move unpacking to __init__?

# for the future:
# TODO integrate interface with category system: make EllipticProduct an abelian variety:
#  - build EllipticProduct as a CartesianProduct of elliptic curves? this should make :meth:`__richcmp__`, :meth:`__len__`, :meth:`__iter__` redundant
#  - give group structure as product of elliptic curve abelian groups.
#    In EllipticProductPoint, inheriting from a product of groups makes sure that :meth:`_richcmp_`, :meth:`__len__`, :meth:`__iter__`, :meth:`__bool__`,
#    and the arithmetic methods :meth:`_add_`, :meth:`_sub_`, :meth:`_neg_`, handling of the zero element are automatically inherited
#  - realize EllipticProduct as a subscheme of ProductProjectiveSpace
#    (EllipticCurve does so with ProjectiveSpace, supports methods on the algebraic scheme (/variety) side
# TODO implement cardinalities
# TODO implement abelian_group()

import sage.all
from sage.structure.element import AdditiveGroupElement
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.richcmp import richcmp, richcmp_method
from builtins import staticmethod
from sage.rings.integer_ring import ZZ

def _unpack(packed):
    r"""
    Helper function for initialization methods.
    When ``packed`` is a tuple/list containing only one iterable element,
    return this element as a tuple. Otherwise, return ``packed`` itself.

    INPUT:

    ``packed`` -- tuple

    This method allows the class constructors below to take factors/components
    as arguments, either packed together in a single list/tuple
    or separately as multiple arguments.

    EXAMPLES::

        sage: from sage.schemes.elliptic_curves.product import _unpack
        sage: lst = [1, 2, 3]
        sage: _unpack(lst)
        (1, 2, 3)
        sage: _unpack([lst])
        (1, 2, 3)
        sage: _unpack((lst,))
        (1, 2, 3)
        sage: _unpack((1,))
        (1,)
        sage: _unpack(1)
        Traceback (most recent call last):
        ...
        TypeError: object of type 'sage.rings.integer.Integer' has no len()
    """
    if len(packed) == 1 and isinstance(packed[0], (tuple, list)):
        unpacked, = packed
        return tuple(unpacked)
    else:
        return tuple(packed)

@richcmp_method
class EllipticProduct(Parent, UniqueRepresentation):
    r"""
    A product of elliptic curves over a general ring.

    In order to construct a product of `E_1 \times \dots \times E_m`,
    call the class constructor with the desired curves (i.e., the factors
    of the product) as arguments::

        sage: E0 = EllipticCurve(ZZ, [1,0])
        sage: E1 = EllipticCurve(ZZ, [2,3])
        sage: A = EllipticProduct(E0, E1, E1, E0)

    The arguments can also be passed as a single tuple or list::
        
        sage: AA = EllipticProduct([E0, E1, E1, E0])
    
    Initializing an elliptic curve product with the same curves
    results in the *same* Python object::

        sage: A is AA
        True

    The base ring of all the factors should be the same::

        sage: EllipticProduct(E0, EllipticCurve(GF(3), [1,0]))
        Traceback (most recent call last):
        ...
        TypeError: all of the given components should be defined over the same base ring
    """
    @staticmethod
    def __classcall__(cls, *curves):
        r"""
        Construct a product of elliptic curves from its factors.

        Method used for compatibility with :class:`UniqueRepresentation`.

        INPUT:

        - `curves`: either multiple arguments, or a single list/tuple,
        where each element is an elliptic curve.
        
        TESTS:

        We check that calling the constructor with bad arguments
        results in an error::

            sage: Fp2.<i> = GF(419^2, modulus=[1,0,1])
            sage: E0 = EllipticCurve(Fp2, [1,0])
            sage: E1 = E0.isogenies_prime_degree(2)[0].codomain()
            sage: A = EllipticProduct(E0, E1)
            sage: A == EllipticProduct([EllipticCurve(E0.a_invariants()),
            ....:                       E1.identity_morphism().codomain()])
            True

            sage: EllipticProduct()
            Traceback (most recent call last):
            ...
            ValueError: there must be at least 2 factors

            sage: P = E0.random_point()
            sage: EllipticProduct(E0, P)
            Traceback (most recent call last):
            ...
            TypeError: all of the given components should be elliptic curves
        """
        return super().__classcall__(cls, *_unpack(curves))

    def __init__(self, *curves):
        r"""
        Construct a product of elliptic curves from its factors.

        INPUT:

        - ``curves``: a tuple of elliptic curves
        
        EXAMPLES::

            sage: E0 = EllipticCurve(ZZ, [1,0])
            sage: E1 = EllipticCurve(ZZ, [2,3])
            sage: A = EllipticProduct(E0, E1); A
            Product of elliptic curves: (Elliptic Curve defined by y^2 = x^3 + x over Integer Ring, Elliptic Curve defined by y^2 = x^3 + 2*x + 3 over Integer Ring)
        """
        super().__init__(self)

        from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
        if len(curves) < 2:
            raise ValueError("there must be at least 2 factors")
        if any(not isinstance(curve, EllipticCurve_generic) for curve in curves):
            raise TypeError("all of the given components should be elliptic curves")
        R = curves[0].base_ring()
        if any(curve.base_ring() != R for curve in curves):
            raise TypeError("all of the given components should be defined over the same base ring")

        self._factors = curves
        self._base_ring = R

    def _element_constructor_(self, *args, **kwds):
        r"""
        Call the :class:`EllipticProductPoint` constructor
        to initialize a point on this product of elliptic curves.

        See :meth:`EllipticProductPoint.__init__` for more details.

        EXAMPLES::

            sage: F = GF(62207)
            sage: E0 = EllipticCurve(j=F(1728))
            sage: A = EllipticProduct(E0, E0)
            sage: P = E0.random_point()
            sage: Q = 2 * P
            sage: PP = A(P, Q)
        """
        return EllipticProductPoint(self, *args, **kwds)
    
    def factors(self):
        r"""
        Return the factors of this product of elliptic curves as a tuple.

        EXAMPLES::

            sage: F = GF(62207)
            sage: E0 = EllipticCurve(j=F(1728))
            sage: E1 = EllipticCurve(j=F(0))
            sage: A = EllipticProduct([E0, E1]); A.factors()
            (Elliptic Curve defined by y^2 = x^3 + x over Finite Field of size 62207,
             Elliptic Curve defined by y^2 = x^3 + 1 over Finite Field of size 62207)
        """
        return self._factors  # that's fine because self._factors is a tuple
    
    def __getitem__(self, n):
        r"""
        Return the ``n``-th elliptic curve of this product.

        INPUT:

        - ``n`` -- integer

        EXAMPLES::

            sage: p = random_prime(2, 1000)
            sage: F = QuadraticField(-p)
            sage: E0 = EllipticCurve(j=F(0))
            sage: E1 = EllipticCurve(j=F(1))
            sage: A = EllipticProduct(E0, E0, E0, E1, E0)
            sage: A[3].j_invariant()
            1

        TESTS::
            sage: A[5]
            Traceback (most recent call last):
            ...
            IndexError: tuple index out of range
        """
        return self._factors[n]

    def __len__(self):
        r"""
        Return the number of factors of this product.

        EXAMPLES::

            sage: p = random_prime(2, 1000)
            sage: F = GF(p)
            sage: A = EllipticProduct(
            ....:         EllipticCurve(j=F(0)),
            ....:         EllipticCurve(j=F(1)),
            ....:         EllipticCurve(j=F.random_element())
            ....:     )
            sage: len(A)
            3
        """
        return len(self._factors)

    def _repr_(self):
        r"""
        Return a string representation of this product of elliptic curves.
        
        EXAMPLES::

            sage: p = 419
            sage: E = EllipticCurve(GF(p), [1,0])
            sage: A = EllipticProduct(E, E); A
            Product of elliptic curves: (Elliptic Curve defined by y^2 = x^3 + x over Finite Field of size 419, Elliptic Curve defined by y^2 = x^3 + x over Finite Field of size 419)
        """
        return "Product of elliptic curves: " + str(self._factors)
        
    def __richcmp__(self, other, op):
        r"""
        Compare two elliptic curve products.
        
        This is done by comparing the underlying tuples of factors.

        EXAMPLES::

            sage: Fp2.<i> = GF(419^2, modulus=[1,0,1])
            sage: E0 = EllipticCurve(Fp2, [1,0])
            sage: E1 = E0.isogenies_prime_degree(2)[0].codomain()
            sage: A = EllipticProduct(E0, E1)
            sage: A == EllipticProduct([EllipticCurve(j=E0.j_invariant()),
            ....:                       E1.identity_morphism().codomain()])
            True
            sage: A is EllipticProduct([EllipticCurve(j=E0.j_invariant()),
            ....:                       E1.identity_morphism().codomain()])
            True
            sage: A == (E0, E1)  # an elliptic curve product is not a tuple
            False
            sage: A != EllipticProduct(E1, E1)
            True
        """
        if not isinstance(other, EllipticProduct):
            return NotImplemented
        return richcmp(self._factors, other._factors, op)

    def dimension(self):
        r"""
        Return the dimension of this product as an algebraic variety.

        Since every factor of the product has dimension 1,
        the output matches the output of :meth:`__len__`.

        EXAMPLES::

            sage: p = random_prime(2, 1000)
            sage: F = GF(p)
            sage: E0 = EllipticCurve(j=F(0))
            sage: E1 = EllipticCurve(j=F(1))
            sage: A = EllipticProduct(E1, E1); A.dimension()
            2
            sage: A = EllipticProduct([E0, E0, E0, E1, E0]); A.dimension()
            5
        """
        return len(self._factors)
    
    def base_ring(self):
        r"""
        Return the base ring of ``self``.

        This is the common base ring of all factors of the product.

        EXAMPLES::

            sage: p = 167
            sage: F = Qp(p, prec=20)
            sage: E = EllipticCurve(j=F(0))
            sage: A = EllipticProduct(E, E, E); A.base_ring()
            167-adic Field with capped relative precision 20
            sage: EE = E.change_ring(F.residue_field())
            sage: EllipticProduct(EE, EE).base_ring()
            Finite Field of size 167
        """
        return self._base_ring
    
    def base_field(self):
        r"""
        Return the base field of ``self``.

        This is the common base field where all the factors are defined.

        EXAMPLES::

            sage: p = 167
            sage: F = GF(p)
            sage: E = EllipticCurve(j=F(0))
            sage: A = EllipticProduct(E, E, E); A.base_field()
            Finite Field of size 167
            sage: E1 = E.change_ring(Zmod(p))
            sage: EllipticProduct(E1, E1, E1).base_field()
            Ring of integers modulo 167
            sage: E2 = EllipticCurve(ZZ, [1,0])
            sage: EllipticProduct(E2, E2).base_field()
            Traceback (most recent call last):
            ...
            ValueError: elliptic curve product not defined over a field
        """
        # TODO need it? should it be an alias of base_ring? should I check instead that the children are instances of EllipticCurve_field?
        if self._base_ring.is_field():
            return self._base_ring
        else:
            raise ValueError("elliptic curve product not defined over a field")
        
    def random_element(self):
        r"""
        Return a random point on this elliptic curve product.

        EXAMPLES::

            sage: p = random_prime(1000)
            sage: F = GF(p^2)
            sage: curves = [EllipticCurve(j=F.random_element())
            ....:   for _ in range(5)]
            sage: PP = EllipticProduct(curves).random_element()
            sage: PP in EllipticProduct(curves)  # random
            ((333*a + 36 : 225*a + 629 : 1), (590*a + 387 : 712*a + 703 : 1))
        """
        return self(*(curve.random_element() for curve in self._factors))
    
    random_point = random_element
    
    def j_invariants(self):
        r"""
        Return the j-invariant of each factor of the product as a tuple.

        EXAMPLES::

            sage: F = GF(419^2)
            sage: E0 = EllipticCurve(F, j=0)
            sage: E1 = EllipticCurve(F, [1,0])
            sage: EllipticProduct(E0, E1).j_invariants() == (0, 1728)
            True  
        """
        return tuple(curve.j_invariant() for curve in self._factors)
    
    # NOTE I removed lift_x. Too much effort to match the existing elliptic curve interface, not strictly needed

class EllipticProductPoint(AdditiveGroupElement):
    r"""
    A point on a product of elliptic curves over a general ring.

    It is represented by a tuple of elliptic curve points.
    If the parent product is `A = E_1 \times \dots \times E_m`, and
    the point is `P = (P_1, \dots, P_m)`, then `P_i` belongs to `E_i`
    for all `i = 1, \dots, m`.

    To construct a point `P`, call the parent object `A` with the desired
    components `P_1, \dots, P_m` as arguments::

    EXAMPLES::

            sage: F = GF(62207)
            sage: E0 = EllipticCurve(j=F(1728))
            sage: A = EllipticProduct(E0, E0, E0)
            sage: P = E0.random_point()
            sage: Q = 2 * P
            sage: PP = A(P, Q, E0(0))
            sage: all(P in E0 for P in PP)
            True

    The arguments can also be passed as a single tuple or list::

        sage: PP == A([P, Q, E0(0)])
        True

    The arguments are automatically coerced to points on the corresponding
    elliptic curve::

        sage: PP == A([P.x(), P.y()], Q, 0)
        True

    Passing 0 as argument returns the point with all zero components::

        sage: A(0) == A(0, 0, 0)
        True
        sage: A(0) == 0
        True
    """
    def __init__(self, parent, *components):
        r"""
        Construct on an elliptic curve product from its components.

        INPUT:

        - ``parent``: an instance of :class:`EllipticProduct`

        - ``components``: either a list, or multiple arguments,
        where each element can be converted into a point on the corresponding
        elliptic curve. The number of components should match the number of 
        factors of the parent product. FIXME strange phrasing

        EXAMPLES::

            sage: F = GF(62207)
            sage: E0 = EllipticCurve(j=F(1728))
            sage: A = EllipticProduct(E0, E0, E0)
            sage: P = E0.random_point()
            sage: Q = 2 * P
            sage: PP = A(P, [Q.x(), Q.y()], E0(0))
            sage: all(P in E0 for P in PP)
            True

        TESTS::

            sage: A(P)
            Traceback (most recent call last):
            ...
            TypeError: number of points does not match parent dimension

            sage: B = EllipticProduct(E0, E0)
            sage: B([P.x(), P.y()])
            Traceback (most recent call last):
            ...
            TypeError: v ... must have 3 components
        """
        super().__init__(parent)

        if components == (0,):
            self._components = tuple(curve(0) for curve in parent._factors)
            return

        components = _unpack(components)
        if len(components) != parent.dimension():
            raise TypeError("number of points does not match parent dimension")
        
        self._components = tuple(curve(point) for curve, point in zip(parent._factors, components))

    def components(self):
        r"""
        Return the components of this point as a tuple of elliptic curve points.

        EXAMPLES::

            sage: F = GF(62207)
            sage: E0 = EllipticCurve(j=F(1728))
            sage: E1 = EllipticCurve(j=F(0))
            sage: A = EllipticProduct([E0, E1])
            sage: P = A(0, E1.lift_x(1)); P.components()
            ((0 : 1 : 0), (1 : 25309 : 1))
        """
        return self._components
    
    def _repr_(self):
        r"""
        Return a string representation of this point.

        EXAMPLES::
            
            sage: F = GF(62207)
            sage: E0 = EllipticCurve(j=F(1728))
            sage: E1 = EllipticCurve(j=F(0))
            sage: A = EllipticProduct([E0, E1])
            sage: P = A(0, E1.lift_x(1)); P
            ((0 : 1 : 0), (1 : 25309 : 1))
        """
        return f"{self._components}"
    
    def __getitem__(self, n):
        r"""
        Return the ``n``-th component of this point.

        INPUT:

        - ``n``: an integer

        OUTPUT: an elliptic curve point
        on the ``n``-th factor of the parent product.

        EXAMPLES::
            
            sage: F = QuadraticField(607)
            sage: E0 = EllipticCurve(j=F(0))
            sage: A = EllipticProduct(E0, E0, E0)
            sage: Q = E0((-1,0,1))  # Q is 2-torsion
            sage: PP = A(Q, Q, 0)
            sage: PP[0] == PP[1] and 2 * PP[1] == PP[2]
            True
        """
        return self._components[n]
    
    def __iter__(self):
        r"""
        Return an iterator over the components of this point.

        EXAMPLES::

            sage: F = QuadraticField(607)
            sage: E0 = EllipticCurve(j=F(0))
            sage: A = EllipticProduct(E0, E0, E0)
            sage: P = E0((2,3,1))
            sage: Q = E0((-1,0,1))
            sage: PP = A([P, P, Q])
            sage: [R == P for R in PP]
            [True, True, False]    
        """
        return iter(self._components)
    
    def __len__(self):
        r"""
        Return the number of components of this point.

        EXAMPLES::

            sage: F = Zmod(75)
            sage: E = EllipticCurve(F, [42, 42])
            sage: A = EllipticProduct(E, E, E)
            sage: P = E((4,7,1))
            sage: PP = A(P, 0, P)
            sage: len(PP)
            3

        TESTS::

            sage: F = GF(random_prime(2000))
            sage: n = randint(2, 10)
            sage: curves = [EllipticCurve(j=F.random_element())
            ....:           for _ in range(n)]
            sage: PP = EllipticProduct(curves).random_point()
            sage: len(PP) == n
            True
        """
        return len(self._components)

    def _richcmp_(self, other, op):
        r"""
        Compare two points on the same elliptic curve product.

        This is done by comparing the underlying component tuples.

        EXAMPLES::

            sage: F = Zmod(100)
            sage: E0 = EllipticCurve([42, 42])
            sage: A = EllipticProduct(E0, E0, E0)
            sage: PP = A(0,0,0)
            sage: PP == A(E0(0), (0,1,0), 0)
            True
        """
        return richcmp(self._components, other._components, op)
    
    def __bool__(self):
        r"""
        Implements the conversion of this point to boolean.

        Returns 0 if all components of this point are the zero element
        on the respective elliptic curves, 1 otherwise.

        EXAMPLES::

            sage: F = Zmod(75)
            sage: E = EllipticCurve(F, [42, 42])
            sage: A = EllipticProduct(E, E)
            sage: P = E((4,7,1))
            sage: [bool(R) for R in (A(0, P), (A(0, 0)))]
            [True, False]
        """
        return any(self)

    def base_ring(self):
        r"""
        Return the base ring of ``self``.

        This is the base ring where all components of the point are defined.

        Alias: :meth:`base_field`

        EXAMPLES::

            sage: F = Qp(167, prec=20)
            sage: E = EllipticCurve(j=F(0))
            sage: A = EllipticProduct(E, E, E);
            sage: P = E.lift_x(1)
            sage: PP = A(P, 0, P); PP.base_ring()
            167-adic Field with capped relative precision 20

            sage: E_res = E.change_ring(F.residue_field())
            sage: A_res = EllipticProduct(E_res, E_res, E_res)
            sage: PP_res = A_res(PP.components()); PP_res.base_ring()
            Finite Field of size 167
        """
        return self.parent().base_ring()
    
    base_field = base_ring
    
    def _add_(self, other):
        r"""
        Add ``self`` and ``other`` component-wise.

        See :meth:`sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint._add_`
        for more details.

        EXAMPLES::

            sage: N = 1113121  # 101 * 103 * 107
            sage: E0 = EllipticCurve(Zmod(N), [1, 0])
            sage: E1 = EllipticCurve(Zmod(N), [0, 1])
            sage: A = EllipticProduct(E0, E1)
            sage: R = A(E0(301098, 673883, 644675), E1(103, 124732, 1))
            sage: T = A(E0(411415, 758555, 255837), E1(4, 6, 2))
            sage: Q = R + T; Q
            ((195489 : 920357 : 107), (63226 : 301196 : 1030301))
            sage: Q[0] == R[0] + T[0] and Q[1] == R[1] + T[1]
            True

            sage: Q + 2 * Q == 3 * Q
            True
        """
        return self.parent()(*(P + Q for P, Q in zip(self._components, other._components)))
    
    def _neg_(self):
        r"""
        Return the additive inverse of ``self``, negating it component-wise.

        EXAMPLES::

            sage: E = EllipticCurve('389a')
            sage: A = EllipticProduct(E, E)
            sage: P = A((-1,-2), (-1,1))
            sage: Q = -P; Q.components()
            ((-1 : 1 : 1), (-1 : -2 : 1))
            sage: Q + P == 0
            True
        """
        return self.parent()(*(-P for P in self))
    
    def _sub_(self, other):
        r"""
        Subtract ``other`` from ``self`` component-wise.

        EXAMPLES::

            sage: E0 = EllipticCurve('389a')
            sage: E1 = EllipticCurve('492b')
            sage: A = EllipticProduct(E0, E1)
            sage: P = A((-1,1), (2, -27))
            sage: Q = A((0, 0), (5, -30))
            sage: (P - Q).components()
            ((4 : 8 : 1), (353 : -6642 : 1))

            sage: (P - Q) + Q == P
            True
        """
        return self.parent()(*(P - Q for P, Q in zip(self._components, other._components)))
    
    def order(self):
        r"""
        Return the order of this point in the product additive group,
        i.e., the least common multiple of the orders of its components.

        The method falls back on
        :meth:`sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint.order`
        on each component,
        hence only succeeds if all components support order computation.

        .. NOTE::

            :meth:`additive_order` is a synonym for :meth:`order`

        EXAMPLES:

        Over a general field, the order is 1 if the point is zero,
        and is not implemented otherwise::

            sage: K.<t> = FractionField(PolynomialRing(QQ,'t'))
            sage: E = EllipticCurve([0, 0, 0, -t^2, 0])
            sage: A = EllipticProduct(E, E)
            sage: P = A((t, 0), (-t, 0))
            sage: P.order()
            Traceback (most recent call last):
            ...
            NotImplementedError: default algorithm not available for order of a point on an elliptic curve over general fields...
            sage: A((0, 0)).additive_order()
            1
            sage: A((0, 0)).order() == 1
            True

        Order computation is implemented over number fields,
        where the order can be infinity::

            sage: E0 = EllipticCurve(QQ, [0, 0, 1, -1, 0])
            sage: E1 = EllipticCurve(QQ, [1, 2, 3, 4, 5])
            sage: A = EllipticProduct(E0, E1)
            sage: P = A((0, 0, 1), E1(0))                    
            sage: P[0].order()
            +Infinity
            sage: P.order()                                  # needs sage.rings.infinity
            +Infinity

        ::

            sage: E = EllipticCurve([0,1])
            sage: A = EllipticProduct(E, E)
            sage: P1 = E([-1, 0])
            sage: P2 = E([2, -3])
            sage: P1.order(), P2.order()
            (2, 6)
            sage: P = A(P1, P2)
            sage: P.order()
            6

        ::

            sage: x = polygen(ZZ)
            sage: K.<a> = NumberField(x^2 - x + 2)
            sage: E0 = EllipticCurve([1, a-1, a+1, -2*a-2, -5*a+7])
            sage: E1 = EllipticCurve([3*a + 4, 6*a - 8])
            sage: A = EllipticProduct(E0, E0, E1)
            sage: P0 = E0.lift_x(a - 3)
            sage: P1 = E1.lift_x(-a)
            sage: P0.order(), P1.order()
            (11, 2)
            sage: PP = A(P0, 0, P1); PP.order()
            22

        An example over finite fields::

            sage: Fp2.<i> = GF(419^2, modulus=[1,0,1])
            sage: E0 = EllipticCurve(j=Fp2(1728))
            sage: E1 = choice(E0.isogenies_prime_degree(2)).codomain()
            sage: A = EllipticProduct(E0, E1)
            
            sage: from sage.schemes.elliptic_curves.ell_field import point_of_order
            sage: Q = A(point_of_order(E0, 3), point_of_order(E1, 5))
            sage: Q.order()
            15
            sage: P = A(point_of_order(E0, 4), 0); P.order()
            4
            sage: (2 * P + Q).order() == 30
            True

        TESTS:

        Check that the order actually gets cached (:issue:`32786`)::

            sage: E = EllipticCurve(GF(31337), [42, 1])
            sage: A = EllipticProduct(E, E, E, E)
            sage: P = E.lift_x(1)
            sage: PP = A(P, P, 0, P)
            sage: hasattr(PP, '_order')
            False
            sage: PP.order()
            15649
            sage: PP._order
            15649
        """
        from sage.arith.functions import lcm
        if not hasattr(self, "_order"):  # not yet known
            self._order = lcm(point.order() for point in self._components)
        return self._order
    
    additive_order = order
    
    def set_order(self, value=None, *, multiple=None, check=True):
        r"""
        Compute and cache the order of each component of this point,
        knowing this order must divide the given ``value`` or ``multiple``,
        applying :meth:`sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint.set_order`
        to each component.

        One can then compute ``self.order()`` easily from the cached orders
        of the components.

        Use this when you know a priori the order of this point, or
        a multiple of the order, to avoid a potentially expensive
        order calculation.

        INPUT:

        - ``value`` -- positive integer
        - ``multiple`` -- positive integer; mutually exclusive with ``value``

        OUTPUT: none

        EXAMPLES::

            sage: # needs sage.rings.finite_rings
            sage: E = EllipticCurve(GF(7), [0, 1])  # This curve has order 12
            sage: A = EllipticProduct(E, E, E)
            sage: G0, G1, G2 = E(5, 0), E(1, 3), E(0, 1)
            sage: [R.order() for R in (G0, G1, G2)]
            [2, 6, 3]
            sage: G = A(G0, G0, G0)
            sage: G.set_order(2)
            sage: 2*G == 0
            True

            sage: # needs sage.rings.finite_rings
            sage: H = A(G0, G1, G2)
            sage: any((2*H == 0, 3*H == 0))
            False
            sage: H.set_order(multiple=12)
            sage: H.order()
            6
            sage: [H_i._order for H_i in H]
            [2, 6, 3]

        This method is useful when the order of the curves of the product
        takes too long to compute (with Sage or using other packages)::

            sage: # needs sage.rings.finite_rings
            sage: p = 2^521 - 1
            sage: prev_proof_state = proof.arithmetic()
            sage: proof.arithmetic(False)  # turn off primality checking
            sage: F = GF(p)
            sage: A = p - 3
            sage: B = 1093849038073734274511112390766805569936207598951683748994586394495953116150735016013708737573759623248592132296706313309438452531591012912142327488478985984
            sage: q = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449
            sage: E = EllipticCurve([F(A), F(B)])  # NIST-P521 curve
            sage: Prod = EllipticProduct(E, E)
            sage: G = Prod.random_point()
            sage: G.set_order(q)
            sage: (G.order() * G).components()  # This takes practically no time.
            ((0 : 1 : 0), (0 : 1 : 0))
            sage: proof.arithmetic(prev_proof_state) # restore state

        Using ``.set_order()`` with a ``multiple=`` argument can
        be used to compute a point's order *significantly* faster
        than calling :meth:`order` if the point is already known
        to be `m`-torsion::

            sage: F.<a> = GF((10007, 23))
            sage: E = EllipticCurve(F, [9,9])
            sage: A = EllipticProduct(E, E, E)
            sage: n = E.order()
            sage: m = 5 * 47 * 139 * 1427 * 2027 * 4831 * 275449 * 29523031
            sage: assert m.divides(n)
            sage: P = n/m * E.lift_x(6747 + a)
            sage: Q = n/m * E.lift_x(5730 + 4919 * a)
            sage: R = 5 * P
            sage: PP = A(P, Q, R)
            sage: assert m * PP == 0
            sage: PP.set_order(multiple=m)             # compute exact order
            sage: PP.order() == m                      # order is now fast to compute
            True
            sage: [factor(m // T._order) for T in PP]  # order of the components is now cached
            [47 * 139, 5, 5 * 47 * 139]

        The algorithm used internally for this functionality is
        :meth:`~sage.groups.generic.order_from_multiple`.
        Indeed, simply calling :meth:`order` on ``P`` would take
        much longer since factoring ``n`` is fairly expensive::

            sage: n == m * 6670822796985115651 * 441770032618665681677 * 9289973478285634606114927
            True

        It is an error to pass a ``value`` equal to `0`::

            sage: # needs sage.rings.finite_rings
            sage: F = GF(7)
            sage: curves = [EllipticCurve(j=F.random_element())
            ....:           for _ in range(4)]
            sage: A = EllipticProduct(curves)
            sage: G = A.random_point()
            sage: G.set_order(0)
            Traceback (most recent call last):
            ...
            ValueError: Value 0 illegal for point order

        It is also very likely an error to pass a value which is not the actual
        order of this point::

            sage: E = EllipticCurve(GF(7), [0, 1])  # This curve has order 12
            sage: A = EllipticProduct(E, E, E)
            sage: G = A.random_point()
            sage: G.set_order(11)
            Traceback (most recent call last):
            ...
            ValueError: The order of P(=...) does not divide 11

        If we set ``check=False`` though, the method runs no sanity checks and
        throws no error::

            sage: E = EllipticCurve(GF(7), [0, 1])  # This curve has order 12
            sage: A = EllipticProduct(E, E, E)
            sage: G = A.random_point()
            sage: G.set_order(11, check=False)  # no complaints
            sage: G.order()
            11

        TESTS:

        Check that some invalid inputs are caught::

            sage: E = EllipticCurve(GF(101), [5,5])
            sage: A = EllipticProduct(E, E)
            sage: P, Q = E.lift_x(11), E.lift_x(53)
            sage: assert 17 * P == 17 * Q == 0
            sage: PQ = A(P, Q)
            sage: PQ.set_order(17, multiple=119)
            Traceback (most recent call last):
            ...
            ValueError: cannot pass both value and multiple
            sage: PQ.set_order(17)
            sage: PQ.set_order(multiple=119+1)
            Traceback (most recent call last):
            ...
            ValueError: previously cached order 17 does not divide given multiple 120
            sage: PQ.set_order(119)
            Traceback (most recent call last):
            ...
            ValueError: Value 119 illegal: 119 * ((11 : 49 : 1), (53 : 24 : 1)) must be the identity

        """
        if check:
            if value is not None:
                if value <= 0:
                    raise ValueError(f"Value {value} illegal for point order")
                if multiple is not None:
                    raise ValueError("cannot pass both value and multiple")

        if multiple is None:
            if not check:
                self._order = ZZ(value)
                return
            multiple = value

        for component in self._components:
            component.set_order(multiple=multiple, check=check)

        if value is not None and check:
            if self.order() != value:  # now the orders of all components are cached so this is fast
                raise ValueError(f"Value {value} illegal: {value} * {self._components} must be the identity")
        
    def weil_pairing(self, other, order, algorithm=None):
        r"""
        Compute the Weil pairing of this point `P = (P_1, \dots, P_m)` 
        with another point `Q = (Q_1, \dots, Q_m)` on the same product.

        The Weil pairing on a product of elliptic curves is the product
        of the Weil pairings on the factor curves of the product:

        .. MATH::

            e_n(P, Q) = e_n(P_1, Q_1) \cdots e_n(P_m, Q_m)

        INPUT:

        - ``other`` -- another point `Q` on the same product as ``self``

        - ``order`` -- integer `n` such that `nP = nQ = (0, \dots, 0)`, where
          `P` is ``self`` and `Q` is ``other``

        - ``algorithm`` -- (default: ``None``) choices are ``'pari'``
          and ``'sage'``. PARI is usually significantly faster, but it
          only works over finite fields. When ``None`` is given, a
          suitable algorithm is chosen automatically.

        OUTPUT: an `n`-th root of unity in the base field of the curve

        EXAMPLES::

            sage: # needs sage.rings.finite_rings
            sage: F.<a> = GF((20201, 2))  # 20201 = 2 * 3 * 7 * 13 * 37 - 1
            sage: E0 = EllipticCurve(j=F(0)); E0.is_supersingular()
            True
            sage: E1 = next(E0.isogenies_degree(21)).codomain()
            sage: A = EllipticProduct(E0, E1)
            sage: P0, Q0 = E0.torsion_basis(7)
            sage: P1, Q1 = E1.torsion_basis(7)
            sage: P, Q = A(P0, P1), A(Q0, Q1)

            sage: # needs sage.rings.finite_rings
            sage: P.weil_pairing(Q, 7)  # random
            3154*a + 5375
            sage: P.weil_pairing(Q, 7).multiplicative_order().divides(7)
            True
            sage: P.weil_pairing(Q, 7 * 13).multiplicative_order().divides(7)
            True

        The Weil pairing is indeed the product of the component-wise
        Weil pairings::
            
            sage: # needs sage.rings.finite_rings
            sage: P.weil_pairing(Q, 7) == P0.weil_pairing(Q0, 7) * P1.weil_pairing(Q1, 7)
            True
            sage: A(P0, P1).weil_pairing(A(P0, Q1), 7) == P1.weil_pairing(Q1, 7)
            True
            sage: A(0, P1).weil_pairing(A(Q0, 0), 7) == F(1)
            True

            sage: # needs sage.rings.finite_rings
            sage: B = EllipticProduct(E0, E0)
            sage: B(P0, Q0).weil_pairing(B(Q0, P0), 7 * 37)
            1

        An error is raised if either point is not `n`-torsion::

            sage: # needs sage.rings.finite_rings
            sage: P.weil_pairing(Q, 37)                                                # needs sage.rings.finite_rings
            Traceback (most recent call last):
            ...
            ValueError: points must both be n-torsion


        TESTS:

        Passing an unknown ``algorithm=`` argument should fail::

            sage: # needs sage.rings.finite_rings
            sage: P.weil_pairing(Q, 7282, algorithm='_invalid_')                        # needs sage.rings.finite_rings
            Traceback (most recent call last):
            ...
            ValueError: unknown algorithm
        """
        from sage.misc.misc_c import prod
        return prod(P.weil_pairing(Q, order, algorithm=algorithm)
                    for P, Q in zip(self._components, other._components))
