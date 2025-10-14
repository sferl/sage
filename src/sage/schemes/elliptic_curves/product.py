r"""
Products of elliptic curves over a general ring

Given `n` elliptic curves `E_1, \dots, E_n` over `R`,
their product `E_1 \times \dots \times E_n` is a principally polarized
abelian variety of dimension `n`. #TODO better docstring?

This module defines a parent class :class:`EllipticProduct` to provide support
for such products, and an element class :class:`EllipticProductPoint` to
represent points on these products, of the form
`(P_1, \dots, P_n) \in E_1 \times \dots \times E_n`.

EXAMPLES::

    sage: Fp2, i = GF(419**2, name='i', modulus=var('x')**2 + 1).objgen()
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
        sage: prod = EllipticProduct(E0, E0) FIXME is this ok or should I use an actual working example?
        sage: prod.isogeny([prod(P0, P0), prod(Q0, Q0)])  # not implemented

AUTHORS:

- Alessandro Sferlazza, Lorenz Panny (2025): Initial version
"""

# TODO answer questions:
# - nicer error messages?
# - handle products as part of the CartesianProduct category?
# - write examples and tests in all docstrings

import sage.all
from sage.structure.element import AdditiveGroupElement
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.richcmp import richcmp, richcmp_method
from builtins import staticmethod
from sage.rings.integer_ring import ZZ

def _unpack(packed): # packed is a tuple
    r"""
    Helper function for initialization methods.
    Used when ``packed`` is a tuple/list containing only one iterable element,
    return this element as a tuple. Otherwise, return ``packed`` itself.

    This method allows the class constructors below to take factors/components
    as arguments, either packed together in a single list/tuple
    or separately as multiple arguments.
    """
    if len(packed) == 1:
        unpacked, = packed
        return tuple(unpacked)
    else:
        return packed

@richcmp_method
class EllipticProduct(Parent, UniqueRepresentation):
    r"""
    A product of elliptic curves over a general ring.
    """
    @staticmethod
    def __classcall__(cls, *curves):
        r"""
        Construct a product of elliptic curves from its factors.

        Method used for compatibility with UniqueRepresentation.
        """
        return super().__classcall__(cls, *_unpack(curves))

    def __init__(self, *curves):
        r"""
        Construct a product of elliptic curves from its factors.

        INPUT:

        - ``curves``: a tuple of elliptic curves

        TODO in the tests: say there should be at least one component
        """
        super().__init__(self)

        from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic
        if not len(curves):
            raise ValueError("there must be at least 1 factor")
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
        """
        return EllipticProductPoint(self, *args, **kwds)
    
    def factors(self):
        r"""
        Return the factors of this product of elliptic curves as a tuple.
        """
        return self._factors  # that's fine because self._curves is a tuple
    
    def __getitem__(self, n):
        r"""
        Return the ``n``-th elliptic curve of this product.

        INPUT:

        - ``n`` -- integer
        """
        return self._factors[n]

    def __len__(self): # TODO needed?
        r"""
        Return the number of factors of this product.
        """
        return len(self._factors)

    def _repr_(self):
        r"""
        Return a string representation of this product of elliptic curves.
        """
        return "Product of elliptic curves: " + str(self._factors)

    def __richcmp__(self, other, op):
        r"""
        Compare two elliptic curve products.
        
        This is done by comparing the underlying tuples of factors.
        """
        if not isinstance(other, EllipticProduct):
            return NotImplemented
        return richcmp(self._factors, other._factors, op)

    def dimension(self):
        r"""
        Return the dimension of this product as an algebraic variety.

        Since every factor of the product has dimension 1,
        the output matches the output of :meth:`__len__`.
        """
        return len(self._factors)
    
    def base_ring(self):
        r"""
        Return the base ring of ``self``.

        This is the common base ring of all factors of the product.
        """
        return self._base_ring
    
    def base_field(self):
        r"""
        Return the base field of ``self``.

        This is the common base field where all the factors are defined.
        """
        if self._base_ring.is_field():
            return self._base_ring
        else:
            raise ValueError("elliptic curve product not defined over a field")
        
    def random_element(self):
        r"""
        Return a random point on this elliptic curve product.
        """
        return self(*(curve.random_element() for curve in self._factors))
    
    random_point = random_element
    
    def j_invariants(self):
        r"""
        Return the j-invariant of each factor of the product as a tuple.
        """
        return tuple(curve.j_invariant() for curve in self._factors)
    
    # NOTE I removed lift_x. Too much effort to match the existing elliptic curve interface, not strictly needed

class EllipticProductPoint(AdditiveGroupElement):
    r"""
    A point on a product of elliptic curves over a general ring.

    It is represented by a tuple of elliptic curve points.
    If the parent product is `E_1 \times \dots \times E_m`, and
    the point is `P = (P_1, \dots, P_m)`, then `P_i` belongs to `E_i`
    for all `i = 1, \dots, m`.
    """
    def __init__(self, parent, *components):
        r"""
        Construct on an elliptic curve product from its components.

        INPUT:

        - ``parent``: an instance of :class:`EllipticProduct`

        - ``components``: either a list, or multiple arguments,
        where each element can be converted into a point on the corresponding
        elliptic curve in the parent product. FIXME strange phrasing
        """
        super().__init__(parent)

        components = _unpack(components)
        if len(components) != parent.dimension():
            raise TypeError("number of points does not match parent dimension")
        
        self._components = tuple(curve(point) for curve, point in zip(parent._factors, components))

    def components(self):
        r"""
        Return the components of this point as a tuple of elliptic curve points.
        """
        return self._components
    
    def _repr_(self):
        r"""
        Return a string representation of this point.
        """
        return f"Point {self._components} on {self.parent()}"
    
    def __getitem__(self, n):
        r"""
        Return the ``n``-th component of this point.

        INPUT:

        - ``n``: an integer

        OUTPUT: an elliptic curve point
        on the ``n``-th factor of the parent product.
        """
        return self._components[n]
    
    def __iter__(self):
        r"""
        Return an iterator over the components of this point.
        """
        return iter(self._components)
    
    def __len__(self):
        r"""
        Return the number of components of this point.
        """
        return len(self._components)

    def _richcmp_(self, other, op):
        r"""
        Compare two points on the same elliptic curve product.

        This is done by comparing the underlying component tuples.
        """
        return richcmp(self._components, other._components, op)
    
    def __bool__(self):
        r"""
        Implements the conversion of this point to boolean.

        Returns 0 if all components of this point are the zero element
        on the respective elliptic curves, 1 otherwise.
        """
        return any(self)

    def base_ring(self):
        r"""
        Return the base ring of ``self``.

        This is the base ring where all components of the point are defined.

        Alias: :meth:`base_field`
        """
        return self.parent().base_ring()
    
    base_field = base_ring
    
    def _add_(self, other):
        r"""
        Add ``self`` and ``other`` component-wise.
        """
        return self.parent()(*(P + Q for P, Q in zip(self._components, other._components)))
    def _neg_(self):
        r"""
        Negate ``self`` component-wise.
        """
        return self.parent()(*(-P for P in self))
    def _sub_(self, other):
        r"""
        Subtract ``other`` from ``self`` component-wise.
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
        """
        from sage.arith.functions import lcm
        if not hasattr(self, "_order"):  # not yet known
            self._order = lcm(point.order() for point in self._components)
        return self._order
    
    def set_order(self, value=None, *, multiple=None, check=True):
        r"""
        Set the cached order of this point (i.e., the value of
        ``self._order``) to the given ``value``.

        Alternatively, when ``multiple`` is given, this method will
        first run :func:`~sage.groups.generic.order_from_multiple`
        to determine the exact order from the given multiple of the
        point order, then cache the result.

        Use this when you know a priori the order of this point, or
        a multiple of the order, to avoid a potentially expensive
        order calculation.
        """
        if multiple is None:
            if not check:
                self._order = ZZ(value)
                return
            multiple = value

        for component in self._components:
            component.set_order(multiple=multiple, check=check)

        if value is not None and check:
            if self.order() != value:  # now the orders of all components are cached so this is fast
                raise ValueError("actual order strictly divides given order")
        
    def weil_pairing(self, other, order, algorithm):
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
        """
        from sage.misc.misc_c import prod
        return prod(P.weil_pairing(Q, order, algorithm=algorithm)
                    for P, Q in zip(self._components, other._components))

if __name__ == "__main__":
    # TODO make them into tests
    from sage.all import (
        GF, var,
        EllipticCurve,
        choice
    )

    p = 419
    Fp2 = GF(p**2, name='i', modulus=var('x')**2 + 1)

    E0 = EllipticCurve(j=Fp2(1728))
    E1 = choice(E0.isogenies_prime_degree(2)).codomain()
    E2 = choice(E1.isogenies_prime_degree(2)).codomain()

    for _ in range(10):
        E1 = choice(E1.isogenies_prime_degree(2)).codomain()

    # product init
    prod3 = EllipticProduct(E0, E1, E2)

    # product richcmp
    print(prod3.factors() == EllipticProduct([E0, E1, E2]).factors())
    print(prod3._factors == EllipticProduct([E0, E1, E2])._factors)
    assert prod3 == EllipticProduct([E0, E1, E2])
    print(f"{prod3 is EllipticProduct([E0.identity_morphism().codomain(), E1, E2]) = }")

    # printing, accessing
    print(f"{prod3 = }\n{prod3[1] = }")

    # base field
    assert prod3.base_field() == Fp2

    # random point
    prod2 = EllipticProduct(E0, E1)
    PP = prod2.random_point()
    
    # point iter, point init
    P0, P1 = PP
    assert PP == prod2(P0, P1)
    assert PP == prod2([P0, P1])
    assert prod2.lift_x(P0.x(), P1.x()) in (PP, -PP, prod2(P0, -P1), prod2(-P0, P1))
    assert prod2.lift_x([P0.x(), P1.x()]) == prod2.lift_x(P0.x(), P1.x())

    try:
        prod2(P0)
    except TypeError:
        pass
    else:
        assert False

    from sage.schemes.elliptic_curves.ell_field import point_of_order
    QQ = prod2(point_of_order(E0, 3), point_of_order(E1, 5))
    assert QQ.order() == 15

    # point init, printing
    P4 = point_of_order(E0, 4)
    RR = prod2([P4.x(), P4.y()], 0)
    print(RR)

    assert QQ + 2 * QQ == 3 * QQ
    assert (QQ + RR).order() == 60

    # set_order, order
    try:
        RRfail = prod2(0, [P4.x(), P4.y()]) # should fail
    except Exception:
        pass
    else:
        assert False

    try:
        RR.set_order(3)
    except Exception:
        pass
    else:
        assert False

    try:
        RR.set_order(multiple=2)
    except Exception:
        pass
    else:
        assert False

    try:
        RR.set_order()
    except Exception:
        pass
    else:
        assert False
    
    RR.set_order(multiple=24)

    RR.set_order(4)

    assert RR == prod2(RR)
    
    from sage.groups.additive_abelian.additive_abelian_wrapper import AdditiveAbelianGroupWrapper
    # print(AdditiveAbelianGroupWrapper.from_generators([PP,QQ,RR]))

    print(prod2.category())


    Fp2, i = GF(419**2, name='i', modulus=var('x')**2 + 1).objgen()
    E0, E1 = EllipticCurve(Fp2, [1,0]), EllipticCurve(Fp2, [3,4])
    E0E1 = EllipticProduct(E0, E1); print(E0E1)
    P0, P1 = E0.lift_x(-1), E1([5, 12])
    PP = E0E1(P0, P1)
    print(all(P in E for P, E in zip(PP, E0E1.factors())))



    