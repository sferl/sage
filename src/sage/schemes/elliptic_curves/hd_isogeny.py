from sage.all import *
from sage.categories.morphism import Morphism
from sage.rings.integer_ring import ZZ
from product import EllipticProduct, EllipticProductPoint

# TODO ._eval

class EllipticProductHom(Morphism):
    # TODO make sure the parent works well (category)
    def __init__(self, domain, codomain, degree_polarized=None, kernel=None):
        r"""
        TODO
        not call it, only call it from EllipticProduct.isogeny()
        or from_kernel
        only there to set attributes for the child classes
        """
        self._domain = domain
        self._codomain = codomain

        if degree_polarized is not None:
            self._degree_polarized = degree_polarized
        if kernel=
        
    @staticmethod
    def from_kernel(domain, kernel, *, degree=None, extra_torsion=None, codomain=None, point_and_image=None, check=True):
        """
        2-dimensional (2^n,2^n)-isogeny E0 x E1 -> E2 x E3
        FUTURE DEVELOPMENT: 4-, 8- dimensional isogenies
        FUTURE DEVELOPMENT: (l, l)-isogenies

        domain: EllipticProduct
        kernel: two points (input is coerced to be a tuple of points on the domain)

        should be only called by class

        if want to make everything quicker, set order of the points before? ### or set degree=None then set_order internally?
        """
        # TODO polarized_degree instead of degree
        # TODO at the end call super().__init__(domain, codomain)
        if not isinstance(domain, EllipticProduct):
            raise TypeError("domain should be an instance of EllipticProduct")
        if domain.dimension() != 2:
            raise NotImplementedError("isogenies between products of elliptic curves are currently only supported in dimension 2")

        # TODO (l, ..., l', ...)-isogenies with l != l' (with possibly l'=1,
        # aka fewer generators, e.g. cyclic isogenies) seem too far to reach soon,
        # so I'm assuming we always have (l,...,l) isogenies
        kernel = tuple(domain(P) for P in kernel)
        # TODO transform into generators??
        if len(kernel) != domain.dimension():
            raise NotImplementedError("the kernel should be given as a basis; only (l, ..., l)-isogenies are currently supported, where the number of kernel generators matches the dimension of the domain")
        if extra_torsion is not None:
            extra_torsion = tuple(domain(P) for P in extra_torsion)
        
        if degree is not None:
            if degree <= 0:
                raise ValueError("degree must be positive")
            for point in kernel:
                point.set_order(ZZ(degree), check=check)
        else:
            degree = kernel[0].order()
            
        if check:
            if list(degree.prime_factors()) != [2]:
                # TODO use is_prime_power
                raise NotImplementedError("Only (2^e, ..., 2^e)-isogenies are supported: the order of all kernel generators must be a power of two")
            
            if any(point.order() != degree for point in kernel): # FIXME this is for later, when we implement odd l
                raise NotImplementedError("Only (l, ..., l)-isogenies are supported: all kernel generators must have the same order")
            
            # check isotropic
            import itertools # TODO imports all over the place or should I put them at the beginning of the function?
            if any(not P.weil_pairing(Q, degree).is_one() for P, Q in itertools.combinations(kernel, 2)):
                raise ValueError("the kernel generators should form a Weil-isotropic subgroup")

        ret = EllipticProductHom(domain, codomain, degree_polarized=degree, kernel=kernel)

        ####### implementation
        # TODO the only supported algorithm is "factored": in HD, we only know how to compute smooth-degree isogenies. Right?
        # TODO do a sort of _compute_factored_isogeny ?? remember degree 2^e can correspond to kernel order 2^(e+2)
        #   if we compute a factored isogeny, then we perhaps need theta structures for intermediate codomains
        if check and extra_torsion is not None:
            # TODO check here that all extra_torsion pts have same degree
            for point, point_above in zip(kernel, extra_torsion):
                if point not in (2 * point_above, 4 * point_above):
                    raise ValueError(f"kernel generator {point} should be equal to 2x or 4x the extra_torsion point {point_above}")
        # TODO integrate thing below
        
        extra_torsion_valuation = 0 # FIXME name?
        if extra_torsion is not None:
            if extra_torsion[0] * 2 == kernel[0]:
                extra_torsion_valuation = 1
            elif extra_torsion[0] * 4 == kernel[0]:
                extra_torsion_valuation = 2
            if check and any(point_above * 2**extra_torsion_valuation != kernel_point
                            for point_above, kernel_point in zip(extra_torsion, kernel)):
                raise ValueError("the extra torsion should all be 2- (or all 4-) torsion above the kernel")    
        else:
            extra_torsion = kernel

        assert all(point_above.order() == (degree * 2**extra_torsion_valuation) for point_above in extra_torsion)
        P, Q = extra_torsion
        
        phi_xonly = compute_2power_2dim_product_isogeny_xonly(domain=domain, above_kernel=extra_torsion,
                                                              extra_torsion_valuation=extra_torsion_valuation)

        ####### quirks
        # TODO use phi_xonly here
        # TODO handle sign choices on y. Need an extra argument/keyword?
        ...

    def _composition_(self, other):
        if not isinstance(self, EllipticProductHom) or not isinstance(other, EllipticProductHom):
            raise TypeError(f'cannot compose {type(self)} with {type(other)}')

        # TODO where to check that codomain(self) == domain(other) ??
        ret = self._composition_impl(self, other)

        if ret is NotImplemented:
            ret = other._composition_impl(self, other)

        if ret is NotImplemented:
            ret = EllipticProductHom_composite.from_factors([other, self])

        return ret

    @staticmethod
    def _composition_impl(left, right):
        return NotImplemented

    def degree_polarized(self): # TODO degree and polarized degree should be two different things... give warning and return polarized_degree^2? only implement polarized_degree()?
        # TODO complain if isogeny times its dual is not a scalar multiplication? or only implement the check for the subclasses?
        return self._degree_polarized
    
    def degree(self):
        return self._degree_polarized ** self.dimension()

    def dual(self):
        raise NotImplementedError
    
    def domain(self):
        return self._domain
    
    def codomain(self):
        return self._codomain

    
# TODO make sure that there's a fast(er) function for evaluation that doesn't do any checks, doesn't construct the isogeny,
# doesn't need to construct it and store it all?

def compute_2power_2dim_product_isogeny_xonly(domain, above_kernel, extra_torsion_valuation=0):
    r"""
    Must kernel[i].set_order() in advance for speed. We do that in the isogeny() method
    """
    # TODO find better name for above_kernel
    num_steps_chain = above_kernel[0].order().valuation(2) - extra_torsion_valuation
    
    # TODO where to check the number of extra steps (here or in mother isogeny function? 
    # note: We wanna get this info when check=False as well.
    # checking it at runtime (and checking point validity) adds overhead. Modify interface to make it faster? 
    # TODO yes do the checks above
        
    assert all(point_above.order() == 2 ** (num_steps_chain + extra_torsion_valuation) for point_above in above_kernel)
    
    P, Q = above_kernel
    

    ####### begin steps ##########
    num_steps_to_do = num_steps_chain
    current_var = domain
    glued = False
    while num_steps_to_do > 0:
        step_done = False
        if not glued:
            # TODO make sure: P, Q are the points above the current kernel, pushed in the last step
            assert isinstance(current_var, EllipticProduct)
            E0, E1 = current_var.factors()
            P_, Q_ = 2**extra_torsion_valuation * P, 2**extra_torsion_valuation * Q
            deg_diagonal_steps = 2**num_steps_to_do / P_[0].weil_pairing(Q_[0], 2**num_steps_to_do).multiplicative_order()
            # TODO or define num_diagonal_steps, for consistency, then deg_diagonal_steps = 2**num_diagonal_steps?
            
            if deg_diagonal_steps > 1:
                Pdiag, Qdiag = (2**(num_steps_to_do) - deg_diagonal_steps) * P_, (2**num_steps_to_do - deg_diagonal_steps) * Q_ 
                assert all(R.order() == 2 ** deg_diagonal_steps for R in (Pdiag, Qdiag))

                # At least one between Pdiag[0] and Qdiag[0] has full order 2**num_diagonal_steps.
                # Otherwise, their weil pairing wouldn't have full order, so e(Pdiag[1], Qdiag[1]) neither, but these points must have full order
                # since P, Q had full order in the beginning
                if Pdiag[0].order() < 2 ** deg_diagonal_steps:
                    Pdiag, Qdiag = Qdiag, Pdiag
                assert Pdiag[0].order() == 2 ** deg_diagonal_steps
                
                # diag_torsion_basis = E0.torsion_basis(2 ** num_diagonal_steps)
                r = Qdiag[0].log(Pdiag[0])  # TODO this should work but I haven't written a proof. check...
                
                ker0 = Pdiag[0]
                ker1 = Qdiag[1] - r * Pdiag[1]
                phi0 = E0.isogeny(ker0)
                phi1 = E1.isogeny(ker1)
                codomain = EllipticProduct(phi0.codomain(), phi1.codomain()) # TODO remove this line once codomain is automatically detected

                step = EllipticProductHom_matrix.from_diagonal((phi0, phi1), domain=current_var, codomain=codomain)
                step_done = True
                # TODO in the future interface: support syntax A = EllipticProduct(E0, E1); A.diagonal_isogeny((phi0, phi1))

            if not step_done and E0.is_isomorphic(E1): # matrix case
                # TODO when generalizing to field extension, or _eval pay attention here. See issue #37427
                psi = E0.isomorphism_to(E1)
                P_, Q_ = 2**(num_steps_to_do - 1) * P_, 2 ** (num_steps_to_do - 1) * Q_
                assert all(R.order() == 2 for R in (P_, Q_))
                for theta in E1.automorphisms(): # TODO do we really need to check all possible thetas? or like only up to sign?
                    if tuple(map(theta * psi, (P_[0], Q_[0]))) == (P_[1], Q_[1]):
                        # endomorphism matrix spotted : E0 x E1 --> E0 x E1
                        mat = [
                            [psi.dual() * theta * psi, psi],
                            [-psi.dual(), theta]
                        ]
                        step = EllipticProductHom_matrix(mat, domain=current_var, codomain=current_var)
                        step_done = True

            if not step_done:
                # no endo no diagonal, let's go with gluing
                P8, Q8 = (2 ** (num_steps_to_do + extra_torsion_valuation - 3) * R for R in (P, Q))
                from theta.theta_isogenies.gluing_isogeny import GluingThetaIsogeny 
                step = GluingThetaIsogeny(P8, Q8)  # TODO adjust interface so that it takes ellipticproductpoint.s, implement hom methods...
                step_done = True
                glued = True
        else:
            P8, Q8 = (2 ** (num_steps_to_do + extra_torsion_valuation - 3) * R for R in (P, Q))
            from theta.theta_isogenies.isogeny import ThetaIsogeny
            step = ThetaIsogeny(current_var, P8, Q8)
            step_done = True
            if step.codomain().is_split():  # TODO implement this
                from theta.theta_isogenies.isomorphism import SplittingIsomorphism
                step = SplittingIsomorphism(current_var) * step  # TODO implement composition correctly
                glued = False

            # TODO different isogeny class in case of no extra torsion??
            
        num_steps_to_do -= step.degree_polarized().valuation(2) # TODO implement this for the theta subclasses, or let them inherit methods somehow
        # TODO this degree_polarized above can be avoided by manually decreasing num_steps_to_do in every option, but this is cleaner.
        current_var = step.codomain()
        P, Q = map(step, (P, Q))
    if glued:
        raise ValueError("2-dimensional isogenies are currently supported only if their domain and codomain are both products of elliptic curves")


class EllipticProductHom_composite(EllipticProductHom):
    def __init__(self, factors, domain, codomain): # TODO just formal combinations? or allow init with single big-torsion kernel basis?
        degree_polarized = prod(phi.degree_polarized() for phi in factors)
        super().__init__(domain, codomain, degree_polarized=degree_polarized)
        self._phis = factors

    @classmethod
    def from_factors(cls, maps, domain=None):
        maps = tuple(maps)
        if not maps and domain is None:
            raise ValueError('need either factors or domain')
        if domain is None:
            domain = maps[0].domain()

        for phi in maps:
            if not isinstance(phi, EllipticProductHom):
                raise TypeError(f'not an isogeny between elliptic curve products: {phi}')
            if phi.domain() != domain:
                raise ValueError(f'isogeny has incorrect domain: {phi}')
            domain = phi.codomain()

        if not maps:
            # maps = (identity_morphism(E),)
            # TODO build identity matrix isogeny from domain
            maps = (domain.identity_morphism(),)

        if len(maps) == 1:
            return maps[0]

        domain = maps[0].domain()
        codomain = maps[-1].codomain()
        return EllipticProductHom_composite(maps, domain, codomain)

    def _call_(self, P):
        for phi in self._phis:
            P = phi(P)  # TODO does this guarantee P passed by value?
        return P

    def _repr_(self):
        from itertools import groupby
        degs = [phi.degree() for phi in self._phis]
        if len(degs) == 1:
            return f'Composite morphism of degree {self._degree}:' \
                    f'\n  From: {self._domain}' \
                    f'\n  To:   {self._codomain}'
        grouped = [(d, sum(1 for _ in g)) for d,g in groupby(degs)]
        degs_str = '*'.join(str(d) + (f'^{e}' if e > 1 else '') for d,e in grouped)
        return f'Composite morphism of degree {self._degree} = {degs_str}:' \
                f'\n  From: {self._domain}' \
                f'\n  To:   {self._codomain}'

    def factors(self):
        return self._phis

    @staticmethod
    def _composition_impl(left, right):
        if isinstance(left, EllipticProductHom_composite):
            if isinstance(right, EllipticProductHom_matrix) and isinstance(left.factors()[0], EllipticProductHom_matrix):
                return EllipticProductHom_composite.from_factors((left.factors()[0] * right,) + left.factors()[1:])
            if isinstance(right, EllipticProductHom_composite):
                return EllipticProductHom_composite.from_factors(right.factors() + left.factors())
            if isinstance(right, EllipticProductHom):
                return EllipticProductHom_composite.from_factors((right,) + left.factors())
        if isinstance(right, EllipticProductHom_composite):
            if isinstance(left, EllipticProductHom_matrix) and isinstance(right.factors()[-1], EllipticProductHom_matrix):
                return EllipticProductHom_composite.from_factors(right.factors()[:-1] + (left * right.factors()[-1],))
            if isinstance(left, EllipticProductHom):
                return EllipticProductHom_composite.from_factors(right.factors() + (left,))
        return NotImplemented

    def dual(self):
        raise NotImplementedError

class EllipticProductHom_matrix(EllipticProductHom):
    def __init__(self, mat, domain, codomain, *, check=True):
        # TODO really include the codomain as argument or deduce it? # XXX for now
        # TODO support non-square matrices (e.g. projections injections)
        # TODO if we detect codomain automatically and there's a whole row set to 0, raise error
        if check:
            if domain is not None and not isinstance(domain, EllipticProduct):
                return TypeError(f"domain should be an elliptic product: {domain}")
            if codomain is not None and not isinstance(codomain, EllipticProduct):
                    return TypeError(f"codomain should be an elliptic product: {codomain}")
            if not isinstance(mat, (list, tuple)) or any(not isinstance(row, (list, tuple)) for row in mat):
                return TypeError(f"both the matrix and its elements should be given as a tuples/lists") # TODO meh, better error messages?
            dim = domain.dimension()
            if len(mat) != dim or any(len(row) != dim for row in mat):
            # FIXME this implicitly checks that matrix should be an iterable with len, and so the
                raise TypeError(f"matrix dimensions should match dimension of the domain (and codomain)")
            from itertools import product
            mat = [list(row) for row in mat]
            for i,j in product(range(dim), range(dim)):
                phi = mat[i][j]
                if phi in ZZ and not phi: # phi in ZZ is a faster check than phi being defined as 0
                    from sage.categories.homset import Hom
                    mat[i][j] = Hom(domain[i], codomain[j]).zero()
                elif phi and phi.domain() != domain[i] or phi.codomain() != codomain[j]:
                    raise TypeError(f"matrix[{i}, {j}] should be a morphism from the {i}-th factor of the domain to the {j}-th factor of the codomain")
            # TODO other checks? do we only want stuff such that self * dual == [polarized_degree]?
                
        self._domain = domain
        self._codomain = codomain
        self._matrix = tuple(tuple(row) for row in mat)  # _matrix is saved as a tuple of tuples

    @staticmethod
    def from_diagonal(diag, domain, codomain):
        mat = [
            [0] * i + [diag[i]] + [0]*(len(diag) - i - 1)
            for i in range(len(diag))
        ]
        return EllipticProductHom_matrix(mat, domain, codomain)

    def _call_(self, P):
        if P not in self.domain():
            raise ValueError(f"point {P} doesn't lie on domain {self._domain}")
        img_components = [
            sum(phi(Pi) for phi, Pi in zip(row, P) if phi)
            for row in self._matrix
        ]
        return self._codomain(img_components)

    @staticmethod
    def _composition_impl(left, right): # TODO check that there's no strange cycle where composite calls matrix who calls composite...
        # TODO make sure parent _composition_ method checks domain of left and codomain of right coincide
        if isinstance(left, EllipticProductHom_matrix) and isinstance(right, EllipticProductHom_matrix):
            domain = right.domain()
            codomain = left.codomain()
            ncols = domain.dimension()
            nrows = codomain.dimension()
            mat = [
                [   
                    sum(
                        alpha * beta for alpha, beta in zip(left._matrix[i], list(zip(*right._matrix))[j])  # TODO check: list(zip(*mat)) should be matrix transposed, right?
                    )
                    for j in range(ncols)
                ]
                for i in range(nrows)
            ]
            return EllipticProductHom_matrix(mat, domain, codomain)

        # TODO check: the following two lines should be implicit in EllipticProductHom._composition_
        # elif isinstance(left, EllipticProductHom) or isinstance(right, EllipticProductHom):
        #     return EllipticProductHom_composite.from_factors((left, right))
        return NotImplemented

    def dual(self):
        matrix_duals = [
            phi.dual() if phi else 0  # TODO handle 0?
            for column in zip(*self._matrix)  # TODO check transposition was correct
            for phi in column
        ]
        return EllipticProductHom_matrix(
            matrix_duals, self._codomain, self._domain
        )

    def _repr_(self):
        dim = self._domain.dimension()
        return f"Matrix of isogenies from {self._domain} to {self._codomain}:" + "".join(f"\n({i}, {j}) of degree {self._matrix[i][j].degree()}"
                                                                                    for i in range(dim) for j in range(dim))

# FIXME fix this hacky workaround
import sys
sys.path.append("..")
sys.path.append("../theta")
from theta.theta_isogenies.product_isogeny_sqrt import EllipticProductIsogeny as ProductIsogenyTheta
from theta.theta_isogenies.product_isogeny_sqrt import EllipticProductIsogenySqrt as ProductIsogenyThetaSqrt
# TODO how to differentiate between sqrt and non-sqrt
class EllipticProductHom_kani(EllipticProductHom, ProductIsogenyTheta):
    def __init__(self, domain, codomain, gluing, steps, splitting, *, check=True):
        # TODO set _degree_polarized, among other things
        ...
        # check maps is gluing, ...steps, splitting
        

    def _call_(self, P):
        if P not in self.domain():
            raise ValueError(f"point {P} doesn't lie on domain {self._domain}")


    @staticmethod
    def _composition_impl(left, right):
        return NotImplemented
    
    def degree_polarized(self):
        return self._degree_polarized

    def _repr_(self):
        return f"Isogeny between products of elliptic curves as polarized abelian varieties, \
            of degree {self._degree_polarized}, where no intermediate step is a product. From: \
            \n  {self._domain} \
            to: \
            \n {self._codomain}"

if __name__ == "__main__":
    from sage.all import (
        GF, var, EllipticCurve
    )
    p = 419
    Fp2 = GF(p**2, name='i', modulus=var('x')**2 + 1)
    E = EllipticCurve(Fp2, [1,0])
    P, Q = E.torsion_basis(2)
    A = EllipticProduct(E, E)
    phiP = E.isogeny(P)
    EP = phiP.codomain()
    B = EllipticProduct(EP, E)
    phiQ = E.isogeny(Q)
    ident = E.identity_morphism()
    Phi = EllipticProductHom_matrix([
        (phiP, 0), (phiP, ident)
    ], A, B)
    Psi = EllipticProductHom_matrix.from_diagonal((phiP, phiP), A, EllipticProduct(EP, EP))
    print(f"{Phi = }")
    print(f"{Psi = }")

    