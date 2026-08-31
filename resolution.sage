from dataclasses import dataclass, field
from itertools import combinations


from time import perf_counter
from contextlib import contextmanager

@contextmanager
def TIMER(label):
    print(f"\n[START] {label}", flush=True)
    start = perf_counter()

    try:
        yield
    finally:
        elapsed = perf_counter() - start
        print(f"[DONE ] {label}: {elapsed:.4f} sec", flush=True)




@dataclass
class ExceptionalComponent:
    """An irreducble expceptional curve"""
    id: int
    name: str
    created_by: int
    tangent_factor: object
    tangent_multiplicity: int = 1

@dataclass
class Chart:
    """An affine chart. 
    Equation = strict transform equation in the chart

    coords = (x_i, y_i , t_i)

    back_to_original = tuple giving (x,y,t) as polynomials in currect coordinates

    component_patches: dict(E_i -> ideal)
    """
    id: int
    ring: object
    equation: object
    coords: tuple
    map_to_original: tuple
    component_patches: dict = field(default_factory=dict)

    parent_chart_id: int | None = None
    parent_blowup_id: int | None = None

    path: tuple = field(default_factory=tuple)
    blowups: list = field(default_factory=list)
    parent_map: object = None
    exceptional_variable: object = None
    chart_type: str | None = None


    def singular_ideal(self):
        F = self.equation

        derivatives = []

        for u in self.coords:
            derivatives.append(F.derivative(u))

        return self.ring.ideal([F] + derivatives)


    def is_sing_at(self, point):
        sub = dict(zip(self.coords, point))
        F = self.equation

        if F.subs(sub) != 0:
            return False

        return all(F.derivative(u).subs(sub) == 0 for u in self.coords)

    def vis_components(self):
        return list(self.component_patches.keys())

    def __repr__(self):
        return (f"Chart(id ={self.id}), path={self.path}, visible={self.vis_components()})")

    def singular_points(self, extra_equations=None):
        I = self.singular_ideal()

        if extra_equations:
            I = I + self.ring.ideal(extra_equations)

        #Using the singular algorithm to compute the GB before calling .variety() has been found for me to be much faster
        GB = I.groebner_basis(
            algorithm='libsingular:slimgb'
        )

        # GB = [1] means empty singular locus
        if len(GB) == 1 and GB[0] == 1:
            return []

        J = self.ring.ideal(list(GB))

        V = J.variety()

        return [
            tuple(P[u] for u in self.coords)
            for P in V
        ]

@dataclass
class BlowupStep:

    id: int
    parent_chart_id: int
    center: tuple

    center_components: list = field(default_factory=list)

    new_components: list = field(default_factory=list)

    children: dict = field(default_factory=dict)



class Resolution:

    def __init__(
        self,
        equation,
        source_ring=None,
        source_images=None,
        infinity_chi=None
    ):
        """
        equation:
            equation in the local 3-variable ring used for resolution.

        source_ring:
            ring in which the original Weierstrass equation lives.

            For a resolution at infinity, equation lives in
                K[X,Y,s]
            with s = 1/t,
            while source_ring is the global
                K[x,y,t].

        source_images:
            images of the global coordinates in Frac(local ring).

            At infinity:
                x -> X/s^(2 chi)
                y -> Y/s^(3 chi)
                t -> 1/s

        infinity_chi:
            None for a finite fibre.
            chi for the infinity chart.
        """

        R = equation.parent()

        self.original_ring = R
        self.original_coords = R.gens()
        self.original_equation = equation

        # NEW
        self.source_ring = (
            R if source_ring is None
            else source_ring
        )

        if source_images is None:
            self.source_images = tuple(R.gens())
        else:
            self.source_images = tuple(source_images)

        self.infinity_chi = infinity_chi
        self.is_infinity = (
            infinity_chi is not None
        )

        self.charts = {}
        self.blowups = {}
        self.components = {}

        self.place = None

        self.skipped_duplicate_points = {}

        self.next_chart_id = 0
        self.next_blowup_id = 0
        self.next_component_id = 0

        root = Chart(
            id=self.new_chart_id(),
            ring=R,
            equation=equation,
            coords=R.gens(),
            map_to_original=R.gens(),
            path=()
        )

        self.root = root
        self.charts[root.id] = root

        self.dynkin_labels = None
        self.cartan_type = None

    def new_chart_id(self):
        i = self.next_chart_id
        self.next_chart_id += 1
        return i

    def new_blowup_id(self):
        i = self.next_blowup_id
        self.next_blowup_id += 1
        return i

    def new_component_id(self):
        i = self.next_component_id
        self.next_component_id += 1
        return i

    def singular_point_above(v):
        """
        Returns the singular point on the surface at t = v (assuming minimal model of course)
        """



    @staticmethod
    def ideal_contains_point(I, chart, point):
        sub = dict(zip(chart.coords, point))

        return all(
            g.subs(sub) == 0
            for g in I.gens()
    )

    def components_containing_point(self, chart_id, q):
        chart = self.charts[chart_id]

        return [
            component_id
            for component_id, I in chart.component_patches.items()
            if self.ideal_contains_point(I, chart, q)
        ]


    # ============================================================
    # Remark 2.19: divisorial vanishing conditions
    # ============================================================

    def pullback_rational_function(self, phi, chart_id):
        """
        Pull a GLOBAL rational function onto a resolution chart.

        For a finite fibre:
            source_ring == original_ring,
            so this is the old behaviour.

        At infinity:
            first make
                t -> 1/s,
                x -> X/s^(2 chi),
                y -> Y/s^(3 chi),
            then pull through the blowup charts.
        """

        chart = self.charts[chart_id]

        Rsrc = self.source_ring
        R0 = self.original_ring
        RU = chart.ring

        K0 = R0.fraction_field()

        if Rsrc is R0:

            if (
                hasattr(phi, "numerator")
                and hasattr(phi, "denominator")
            ):
                num0 = R0(phi.numerator())
                den0 = R0(phi.denominator())
            else:
                num0 = R0(phi)
                den0 = R0.one()

            local_phi = (
                K0(num0) / K0(den0)
            )

        else:

            source_map = Rsrc.hom(
                list(self.source_images),
                K0
            )

            if (
                hasattr(phi, "numerator")
                and hasattr(phi, "denominator")
            ):
                num_src = Rsrc(phi.numerator())
                den_src = Rsrc(phi.denominator())
            else:
                num_src = Rsrc(phi)
                den_src = Rsrc.one()

            local_phi = (
                source_map(num_src)
                / source_map(den_src)
            )

        
        psi = R0.hom(
            list(chart.map_to_original),
            RU
        )

        num = R0(local_phi.numerator())
        den = R0(local_phi.denominator())

        KU = RU.fraction_field()

        return (
            KU(psi(num))
            / KU(psi(den))
        )

    @staticmethod
    def common_denominator(R, fracs):
        """
        Clear denominators without polynomial lcm(). Calling lcm() is a bit too slow...
        """

        if len(fracs) == 0:
            raise ValueError(
                "Need at least one rational function"
            )

        denoms = [
            R(h.denominator())
            for h in fracs
        ]

        # We can do a quick check if all denominators are equal (makes this faster)
        d0 = denoms[0]

        if all(d == d0 for d in denoms):

            return (
                d0,
                [
                    R(h.numerator())
                    for h in fracs
                ]
            )

        # Otherwise, use product
        g = prod(denoms)

        nums = []

        for h, d in zip(fracs, denoms):

            # I don't want to call lcm or quo_rem (slow)
            multiplier = R.one()

            skipped = False

            for e in denoms:

                if not skipped and e == d:
                    skipped = True
                    continue

                multiplier *= e

            nums.append(
                R(h.numerator()) * multiplier
            )

        return g, nums


    
       

    @staticmethod
    def symbolic_power_on_surface(chart, P, w):
        r"""
        Return an ambient-ring ideal representing the symbolic power

            p^(w)

        of the height-one prime p on the smooth resolved surface.
        """

        if w < 0:
            raise ValueError(
                "Symbolic power exponent must be nonnegative"
            )

        R = chart.ring
        F = R(chart.equation)

        I_surface = R.ideal([F])
        P_surface = P + I_surface

        if w == 0:
            return R.ideal([1])

        if w == 1:
            return P_surface

        gens = [R(g) for g in P.gens()]



        for i in range(len(gens)):
            for j in range(i + 1, len(gens)):

                g1 = gens[i]
                g2 = gens[j]

                pair = R.ideal([g1, g2])

                
                try:
                    coeffs = F.lift(pair.gens())
                except (ValueError, TypeError):
                    continue

                if len(coeffs) != 2:
                    continue

                a = R(coeffs[0])
                b = R(coeffs[1])

                
                assert a*g1 + b*g2 == F

                candidates = []

            
                if b not in P_surface:
                    candidates.append((g1, b))

                
                if a not in P_surface:
                    candidates.append((g2, a))

                for local_eq, s in candidates:

                    S = R.ideal([s])

         
                    P_local = P_surface.saturation(S)[0]

                    principal_local = (
                        I_surface
                        + R.ideal([local_eq])
                    ).saturation(S)[0]

                    if P_local != principal_local:
                        continue

                  
                    J = (
                        I_surface
                        + R.ideal([local_eq**w])
                    )

                    symbolic = J.saturation(S)[0]

                    return symbolic

        raise RuntimeError(
            f"Could not principalize divisor ideal on chart {chart.id}. "
            f"Generators were {list(P.gens())}"
        )

    @staticmethod
    def old_symbolic_power_on_surface(chart, P, w):
        r"""
        Return an ambient-ring ideal representing the symbolic power

            p^(w)  in  A = R/(F),

        where P is the inverse image in R of the height-one prime p.
        """
        if w < 0:
            raise ValueError("Symbolic power exponent must be nonnegative")

        R = chart.ring

        if w == 0:
            return R.ideal([1])

        I_surface = R.ideal([chart.equation])
        P_surface = P + I_surface

        if w == 1:
            return P_surface

        J = I_surface + P_surface**w
        target_radical = P_surface.radical()

        for Q in J.primary_decomposition():
            if Q.radical() == target_radical:
                return Q

        raise RuntimeError(
            f"Could not find the P-primary component for symbolic power {w} "
            f"on chart {chart.id}"
        )

    @classmethod
    def order_along_prime(cls, chart, P, h, max_order=50):
        r"""
        Compute ord_D(h) for a polynomial h on a smooth resolution chart,
        using

            ord_D(h) = max{m : h in P_D^(m)}.
        """
        R = chart.ring
        h = R(h)

        if h == 0:
            return Infinity

        for w in range(1, max_order + 1):
            Pw = cls.symbolic_power_on_surface(chart, P, w)
            if h not in Pw:
                return w - 1

        raise RuntimeError(
            f"ord_D(h) is at least {max_order}; increase max_order"
        )

    @staticmethod
    def kernel_mod_ideal(R, basis_polys, I):
        r"""
        Return the coefficient space of vectors a=(a_i) satisfying

            sum_i a_i basis_polys[i] in I.

        The coefficients a_i lie in R.base_ring().
        """
        K = R.base_ring()
        n = len(basis_polys)

        if n == 0:
            return VectorSpace(K, 0)

        remainders = [R(I.reduce(R(f))) for f in basis_polys]

        monomials = set()
        for r in remainders:
            monomials.update(r.dict().keys())

        if len(monomials) == 0:
            return VectorSpace(K, n)

        monomials = sorted(monomials)

        rows = []
        for mon in monomials:
            rows.append([
                r.dict().get(mon, K.zero())
                for r in remainders
            ])

        M = Matrix(K, rows)
        return M.right_kernel()

    def component_leaf_patch(self, component_id):
        """
        Choose a resolved (leaf) affine chart on which the exceptional
        component ``component_id`` is visible, and return (chart, ideal).
        """
        if component_id not in self.components:
            raise ValueError(f"Unknown exceptional component {component_id}")

        for chart_id in self.leaf_chart_ids():
            chart = self.charts[chart_id]
            if component_id in chart.component_patches:
                return chart, chart.component_patches[component_id]

        raise RuntimeError(
            f"Exceptional component {component_id} is not visible on any leaf chart"
        )

    def strict_transform_ideal_on_chart(self, I_root, chart_id):
        """
        Propagate an ideal from the original chart to ``chart_id`` by taking
        strict transforms along the unique path in the resolution tree.
        """
        cache = {self.root.id: I_root}

        def recurse(cid):
            if cid in cache:
                return cache[cid]

            chart = self.charts[cid]
            parent_I = recurse(chart.parent_chart_id)

            I = self.strict_transform_ideal(
                parent_I,
                chart.parent_map,
                chart.exceptional_variable,
                chart.ring
            )

            cache[cid] = I
            return I

        return recurse(chart_id)

    def identity_component_leaf_patch(self):
        r"""
        Return one leaf-chart patch of the non-exceptional component of the
        fibre t = self.place, i.e. the strict transform of the original
        Weierstrass fibre.

        This is the component Theta_{v,0} meeting the zero section.
        """
        if self.place is None:
            raise ValueError("Resolve a fibre first so that self.place is known")

        R = self.original_ring
        x, y, t = self.original_coords
        I_fibre = R.ideal([t - self.place])

        for chart_id in self.leaf_chart_ids():
            chart = self.charts[chart_id]
            I = self.strict_transform_ideal_on_chart(I_fibre, chart_id)

            if I != chart.ring.ideal(1):
                return chart, I

        raise RuntimeError(
            "The strict transform of the original fibre was not visible on any leaf chart"
        )

    def impose_prime_vanishing(self, basis, chart, P, required_order,
                               max_order=50):
        r"""
        Apply Remark 2.19 for one prime divisor D.

        Starting with rational functions phi_i spanning a linear system,
        return a basis of the subspace satisfying

            ord_D(phi) >= required_order.
        """
        if required_order < 0:
            raise ValueError("required_order must be nonnegative")

        basis = list(basis)
        if len(basis) == 0 or required_order == 0:
            return basis

        pulled = [
            self.pullback_rational_function(phi, chart.id)
            for phi in basis
        ]

        g, nums = self.common_denominator(chart.ring, pulled)

        ord_g = self.order_along_prime(
            chart,
            P,
            g,
            max_order=max_order
        )

        w = required_order + ord_g
        Pw = self.symbolic_power_on_surface(chart, P, w)

        ker = self.kernel_mod_ideal(chart.ring, nums, Pw)

        new_basis = []
        for a in ker.basis():
            phi = sum(a[i] * basis[i] for i in range(len(basis)))
            new_basis.append(phi)

        return new_basis

    def impose_exceptional_vanishing(
    self,
    basis,
    component_id,
    required_order,
    max_order=50
):
        """
        Apply Remark 2.19 to one exceptional component,
        using its birth chart.
        """
        '''print(
        "EXCEPTIONAL:",
        "component =", component_id,
        "order =", required_order,
        flush=True
    )'''

        chart, P, e, f = self.component_birth_patch(
            component_id
        )

        '''print(
            "  got birth chart",
            chart.id,
            flush=True
        )'''

        pulled = []

        for i, phi in enumerate(basis):

            '''print(
                "  pulling basis element",
                i,
                flush=True
            )'''

            h = self.pullback_rational_function(
                phi,
                chart.id
            )

            pulled.append(h)

            '''print(
                "    denominator =",
                h.denominator(),
                flush=True
            )'''

        '''print(
            "  all pullbacks finished",
            flush=True
        )'''

        g, nums = self.common_denominator(
            chart.ring,
            pulled
        )

        '''print(
            "  common denominator finished",
            flush=True
        )'''

        ord_g = 0

        for w in range(1, max_order + 1):

            Pw = self.symbolic_power_birth_chart(
                chart,
                P,
                e,
                f,
                w
            )

            if g not in Pw:
                ord_g = w - 1
                break

        else:
            raise RuntimeError(
                f"Denominator order >= {max_order}"
            )

        w = required_order + ord_g

        Pw = self.symbolic_power_birth_chart(
            chart,
            P,
            e,
            f,
            w
        )

        ker = self.kernel_mod_ideal(
            chart.ring,
            nums,
            Pw
        )

        new_basis = []

        for a in ker.basis():

            phi = sum(
                a[i] * basis[i]
                for i in range(len(basis))
            )

            new_basis.append(phi)

        return new_basis

    def impose_identity_vanishing(self, basis, required_order, max_order=50):
        """Apply Remark 2.19 to the identity component Theta_{v,0}."""
        chart, P = self.identity_component_leaf_patch()
        return self.impose_prime_vanishing(
            basis,
            chart,
            P,
            required_order,
            max_order=max_order
        )

    def impose_vertical_conditions(self, basis, identity_order=0,
                                   exceptional_orders=None, max_order=50):
        r"""
        Impose a collection of vertical vanishing conditions on this fibre.

        INPUT:
            basis               -- basis of rational functions
            identity_order      -- required order on Theta_{v,0}
            exceptional_orders  -- dict {component_id: required_order}

        OUTPUT:
            a basis of the simultaneous solution space.

        The conditions are imposed one at a time; after each condition the
        returned kernel basis becomes the basis for the next condition.
        """
        if exceptional_orders is None:
            exceptional_orders = {}

        current = list(basis)

        if identity_order > 0:
            current = self.impose_identity_vanishing(
                current,
                identity_order,
                max_order=max_order
            )

        for component_id, order in exceptional_orders.items():
            if order <= 0:
                continue

            current = self.impose_exceptional_vanishing(
                current,
                component_id,
                order,
                max_order=max_order
            )

            if len(current) == 0:
                break

        return current


    '''It is completely possible for at some blowup to the singular point not to be at (0,0,0). 
        For simplicities sake it will be useful to recenter the point.

        to analyze the exceptional divisor, we will also need the tangent cone
    '''

    def recenter_and_tcone(self, chart, point):
        R = chart.ring

        x,y,t = chart.coords
        a,b,c = point

        G = R(chart.equation.subs({x: x + a, y: y + b, t: t + c}))

        if G == 0: raise ValueError("Equation is 0: recent and tcone method")

        terms = G.dict()

        m = min(sum(exp) for exp, coeff in terms.items() if coeff != 0)

        T = R.zero()

        for exp, coeff in terms.items():
            if sum(exp) == m:
                mon = prod(z^e for z,e in zip((x,y,t), exp))
                T += coeff*mon

        return G,m,T


    '''We are also gonna need to be able to compute the strict transform after a blowup'''

    @staticmethod
    def divide_factor(F, d):
        R = F.parent()

        if F == 0:
            raise ValueError("Cannot divide factor from zero polynomial.")

        gens = R.gens()

        # Which variable is d?
        try:
            i = gens.index(d)
        except ValueError:
            raise ValueError(f"{d} is not a generator of the polynomial ring.")

        terms = F.dict()

        m = min(exp[i] for exp, coeff in terms.items() if coeff != 0)

        if m == 0:
            return F

        # Build F / d^m manually
        answer = R.zero()

        for exp, coeff in terms.items():
            if coeff == 0:
                continue

            new_exp = list(exp)
            new_exp[i] -= m

            monomial = prod(z^e for z, e in zip(gens, new_exp))
            answer += coeff * monomial

        return answer


    '''HOW TO COMPUTE INTERSECTION OF TWO COMPONENTS,n namely I need to be able to 
    get the intersection of an ideal I with a new one J, where I need to pull I through the new chart phi'''
    @staticmethod
    def strict_transform_ideal(I, phi, exceptional_variable, ring_child):
        #since I could have multiple generators, we cannot simply divide by the exceptional variable. Instead
        #we have to perform a more sophisticated operation, namely saturation. (These
        #multiple generators come from the fact that a curve C < S has dimension 1 in A^3, hence will need two equations defining it)

        generators = [phi(g) for g in I.gens()]

        J = ring_child.ideal(generators)

        E = ring_child.ideal([exceptional_variable])

        return J.saturation(E)[0]


    def blowup(self, chart_id, point=(0,0,0)):
        '''Returns {
            'x': x_chart
            'y': y_chart
            't': t_chart
        }'''

        parent = self.charts[chart_id]

        if not parent.is_sing_at(point):
            raise ValueError(f"{point} is not singular point of chart {chart_id}.")


        #need to determine which existing exceptional components pass through the center of this blowup
        center_components = []

        for component_id, I in parent.component_patches.items():

            if self.ideal_contains_point(I, parent, point):
                center_components.append(component_id)


        blowup_id = self.new_blowup_id()

        G, mult, Q = self.recenter_and_tcone(parent, point)

        tangent_factors = list(Q.factor())

        new_components = []


        for factor, exponent in tangent_factors:

            component_id = self.new_component_id()

            E = ExceptionalComponent(
                id = component_id,
                name = f"E_{component_id}",
                created_by =blowup_id,
                tangent_factor= factor,
                tangent_multiplicity = int(exponent)
            )

            self.components[component_id] = E
            new_components.append(component_id)

        step = BlowupStep(
            id = blowup_id,
            parent_chart_id=parent.id,
            center=point,
            center_components=center_components,    
            new_components=new_components
        )

        self.blowups[blowup_id] = step
        parent.blowups.append(blowup_id)

        #TEMPORARY DEBUGGER
        # TEMPORARY DEBUG PRINT
        """print(
            f"Blowup {blowup_id}: "
            f"chart={parent.id}, "
            f"center={point}, "
            f"old={center_components}, "
            f"new={new_components}"
        )"""

        children = {}

        for chart_type in ('x', 'y', 't'):
            child = self.make_blowup_chart(
                parent = parent,
                point=point, 
                blowup_id = blowup_id, 
                chart_type = chart_type, 
                tangent_factors = tangent_factors, 
                component_ids=new_components
            )
            children[chart_type] = child
            step.children[chart_type] = child.id

        return step



    def make_blowup_chart(self, parent, point, blowup_id, chart_type, tangent_factors, component_ids):
        R_parent = parent.ring
        K = R_parent.base_ring()
        level = len(parent.path) + 1

        R_child = PolynomialRing(K, names=(f"x{level}_{chart_type}", f"y{level}_{chart_type}", f"t{level}_{chart_type}"))

        X,Y,T = R_child.gens()

        a,b,c = [R_child(z) for z in point]

        if chart_type == 'x':
            images = (a + X, b + X*Y, c + X*T)
            exceptional_variable = X
            tangent_images = (R_child(1), Y, T)
        elif chart_type == 'y':
                    images = (a + X*Y, b + Y, c + Y*T)
                    exceptional_variable = Y
                    tangent_images = (X, R_child(1), T)
        elif chart_type == 't':
                    images = (a + T*X, b + T*Y, c + T)
                    exceptional_variable = T
                    tangent_images = (X, Y, R_child(1))
        else:
            raise ValueError(f"Unknown chart chart_type: {chart_type}")

        #this is our map doing the substitution
        phi = R_parent.hom(images, R_child)

        transform = phi(parent.equation)

        strict_equation = self.divide_factor(transform, exceptional_variable)

        map_to_original = tuple(phi(f) for f in parent.map_to_original)

        '''NEED TO GET STRICT TRANSFORM OF OLD EXCEPTIONAL COMPONENTS'''

        new_components = {}

        for component_id, old_I in parent.component_patches.items():
        
                     new_I = self.strict_transform_ideal(old_I, phi, exceptional_variable, R_child)

                     if new_I != R_child.ideal(1):
                          new_components[component_id] = new_I

        #need to get new exceptional components:

        tangent_phi = R_parent.hom(tangent_images, R_child)

        for component_id, (factor, exponent) in zip(component_ids, tangent_factors):
             local_factor = tangent_phi(factor)

             #if factor is nonzero constant, its outside the affine chart:
             if local_factor.is_constant() and local_factor != 0:
                  continue

             #else we have a new curve whose ideal is (exceptional_variable, local_factor)
             new_components[component_id] = R_child.ideal([exceptional_variable, local_factor])

        #we now make a child chart:

        child_id = self.new_chart_id()

        child = Chart(
            id = child_id, 
            ring = R_child, 
            equation=strict_equation,
            coords=(X,Y,T), 
            map_to_original=map_to_original,
            component_patches = new_components,
            parent_chart_id= parent.id,
            parent_blowup_id = blowup_id,
            path = parent.path + ((blowup_id, chart_type),),
            parent_map=phi,
            exceptional_variable=exceptional_variable,
            chart_type=chart_type
        )

        self.charts[child_id] = child

        return child

    @staticmethod
    def exceptional_point_key(chart_type, point):
        """
        Convert a point on an affine exceptional-divisor chart
        to a canonical projective point [X:Y:T].
        """

        x, y, t = point

        if chart_type == 'x':
            # x-chart has projective coordinates [1:y:t]
            P = (x.parent()(1), y, t)

        elif chart_type == 'y':
            # y-chart has projective coordinates [x:1:t]
            P = (x, y.parent()(1), t)

        elif chart_type == 't':
            # t-chart has projective coordinates [x:y:1]
            P = (x, y, t.parent()(1))

        else:
            raise ValueError(f"Unknown chart type: {chart_type}")

        # Normalize projectively:
        # divide by the first nonzero coordinate.
        for a in P:
            if a != 0:
                return tuple(z / a for z in P)

        raise ValueError("Invalid projective point.")

    @staticmethod
    def on_new_exceptional(chart_type, point):
        X,Y,T = point
        if chart_type == 'x':
            return X == 0
        if chart_type == 'y':
             return Y == 0 and X == 0
        if chart_type == 't':
             return T == 0 and X == 0 and Y == 0
        raise ValueError(f"Unknown chart type {chart_type}")
    

    '''Now we do DFS'''
    def resolve(self, point, chart_id = None, max_depth=50):
         """resolves singular point of chart"""

         self.place = point[2]

         if chart_id is None: chart_id = self.root.id

         chart = self.charts[chart_id]

         if not chart.is_sing_at(point):
              raise ValueError(f"{point} is not a singular point of chart {chart_id}")
         self.resolve_point(chart_id, point, depth=0, max_depth = max_depth)

    def resolve_point(self, chart_id, point, depth, max_depth):
        if depth > max_depth:
              raise RuntimeError(f"Max DFS depth exceeded at chart {chart_id}")

        """print(
                 "  " * depth +
                 f"Chart {chart_id}: {len(point)} singular point(s)")"""
        step = self.blowup(chart_id, point)

        seen_points = []
        points_to_resolve = []

        for chart_type, child_id in step.children.items():

            child = self.charts[child_id]

            X, Y, T = child.coords

            if chart_type == 'x':
                exceptional_variable = X

            elif chart_type == 'y':
                exceptional_variable = Y

            elif chart_type == 't':
                exceptional_variable = T

            else:
                raise ValueError(
                    f"Unknown chart type: {chart_type}"
                )

            # Find singular points lying above the blowup center
            points = child.singular_points(
                extra_equations=[exceptional_variable]
            )

            for q in points:

                key = self.exceptional_point_key(
                    chart_type,
                    q
                )

                # Same projective point may appear in another affine blow up
                if key in seen_points:
                    """print(
                        f"Skipping duplicate point {q} "
                        f"in {chart_type}-chart; "
                        f"projective point = {key}"
                    )"""
                    self.skipped_duplicate_points.setdefault(child_id, []).append(q)
                    continue

                seen_points.append(key)

                points_to_resolve.append(
                    (child_id, q)
                )


        # Resolve each GEOMETRIC singular point exactly once
        for child_id, q in points_to_resolve:

            self.resolve_point(
                child_id,
                q,
                depth + 1,
                max_depth
            )

    
    def leaf_chart_ids(self):
        """
        returns leaves in the resolution tree, i.e. we should check that they are smooth
        """
        blown_up_charts = {
            step.parent_chart_id
            for step in self.blowups.values()
        }

        return [
            chart_id
            for chart_id in self.charts
            if chart_id not in blown_up_charts
        ]

    def components_intersect_in_step(self, step, i, j):
        """
        Check whether components components i and j intersect in one of the
        child charts produced by this particular blowup.
        """
        for child_id in step.children.values():
            child = self.charts[child_id]

            if self.components_intersect_in_chart(child, i, j):
                return True

        return False

    def components_intersect_in_chart(self, chart, i, j):
        #gotta check if they even exist
        if i not in chart.component_patches:
            return False

        if j not in chart.component_patches:
            return False

        I = chart.component_patches[i]

        J = chart.component_patches[j]

        K = I + J + chart.ring.ideal([chart.equation])
        intersects = chart.ring.one() not in K

        '''if intersects:
            print(
            f"E_{i} intersects E_{j} "
            f"in chart {chart.id}, "
            f"path={chart.path}"
            )''' #bug fixing

        
        return intersects #Weak Hilbert's Nullstellensatz


    def intersecting_edges(self):
         
         edges = set()

         for chart_id in self.leaf_chart_ids():
              chart = self.charts[chart_id]

              visible = list(chart.component_patches.keys())

              for i,j in combinations(visible, 2):
                   if self.components_intersect_in_chart(chart, i, j):
                        edges.add(tuple(sorted((i,j))))
         return edges

    def intersection_graph(self):
         G = Graph()

         G.add_vertices(self.components.keys())

         for blowup_id in sorted(self.blowups):
              step = self.blowups[blowup_id]

              old = step.center_components
              new = step.new_components

              for i,j in combinations(old, 2):
                   if G.has_edge(i,j):
                        G.delete_edge(i,j)
              L = old + new
              for i,j in combinations(L, 2):
                   if i not in new and j not in new:
                        continue
                   if self.components_intersect_in_step(step, i,j):
                        G.add_edge(i,j)

         return G

    def section_intersects_component(self, I_P, component_id, chart_id):
        chart = self.charts[chart_id]
        
        I = I_P
        current_chart = self.root

        for blowup_id, chart_type in chart.path:
             step = self.blowups[blowup_id]


             child_id = step.children[chart_type]
             child = self.children[child_id]

             I = self.strict_transform_ideal(I, child.parent_map, child.exceptional_variable, child.ring)

             current_chart = child

        I_Theta = chart.component_patches[component_id]
        K = I + I_Theta + chart.ring.ideal([chart.equation])

        return chart.ring.one() not in K

    def dynkin_labeling(self, cartan_type):
        """
        Returns an isomorphism which maps the intersection graph computed here with the associated dynkin diagram
        """

        G = self.intersection_graph()

        T = CartanType(cartan_type)

        H = T.dynkin_diagram().to_undirected()

        isomorphic, labeling = G.is_isomorphic(
            H,
            certificate=True
        )

        if not isomorphic:
            raise ValueError(
                f"Exceptional graph is not of Cartan type {cartan_type}"
            )
        self.dynkin_labels = labeling
        self.cartan_type = T
        return labeling

    @staticmethod
    def symbolic_power_birth_chart(chart, P, e, f, w):
        r"""
        Compute the symbolic power of an exceptional component
        on one of its birth charts.

        Here
            P = (e,f)
            F = A*e + B*f.

        If B is nonzero generically on P, then e is a local
        equation for the divisor.

        If A is nonzero generically on P, then f is a local
        equation for the divisor.
        """

        '''print(
            "  symbolic power",
            w,
            "chart",
            chart.id,
            flush=True
        )'''

        if w < 0:
            raise ValueError(
                "Symbolic power exponent must be nonnegative"
            )

        R = chart.ring

        if w == 0:
            return R.ideal([1])

        F = R(chart.equation)

        I_surface = R.ideal([F])
        P_surface = P + I_surface

        if w == 1:
            return P_surface

        e = R(e)
        f = R(f)


        J = R.ideal([e, f])

        coeffs = F.lift(J.gens())

        if len(coeffs) != 2:
            raise RuntimeError(
                "Unexpected lift length on birth chart."
            )

        A = R(coeffs[0])
        B = R(coeffs[1])

        if A*e + B*f != F:
            raise ArithmeticError(
                "Lift of the surface equation failed."
            )

        '''print(
            "    A in P =",
            A in P_surface,
            flush=True
        )'''

        '''print(
            "    B in P =",
            B in P_surface,
            flush=True
        )'''

        if B not in P_surface:

            local_eq = e
            unit = B

            '''print(
                "    using exceptional variable as local equation",
                flush=True
            )'''

        elif A not in P_surface:

            local_eq = f
            unit = A

            '''print(
                "    using tangent factor as local equation",
                flush=True
            )'''

        else:

            raise RuntimeError(
                f"Neither birth-chart generator principalizes "
                f"component on chart {chart.id}."
            )


        Jw = (
            I_surface
            + R.ideal([local_eq**w])
        )

        symbolic = Jw.saturation(
            R.ideal([unit])
        )[0]

        return symbolic

    def component_birth_patch(self, component_id):
        """
        Return a chart on which component_id is newly created.

        OUTPUT:
            chart, P, e, f

        where

            P = (e, f),

        e is the exceptional coordinate, and f is the tangent-factor
        equation cutting out this irreducible exceptional component.
        """

        if component_id not in self.components:
            raise ValueError(
                f"Unknown exceptional component {component_id}"
            )

        component = self.components[component_id]
        blowup_id = component.created_by

        step = self.blowups[blowup_id]

        for chart_type, child_id in step.children.items():

            chart = self.charts[child_id]

            if component_id not in chart.component_patches:
                continue

            P = chart.component_patches[component_id]

            gens = list(P.gens())

            if len(gens) != 2:
                continue

            e = chart.exceptional_variable

            # Determine which generator is the non-exceptional one.
            if gens[0] == e:
                f = gens[1]

            elif gens[1] == e:
                f = gens[0]

            else:
                # Ideally should not occur for a newly-created component.
                continue

            return chart, P, e, f

        raise RuntimeError(
            f"Could not find birth chart for component {component_id}"
        )


    def section_intersection(self, P):
        """
        Returns

            (P . Theta_{v,1}, ..., P . Theta_{v,r})

        in the ordering agreeing with Sage's Cartan matrix numbering.

        The zero vector means that P meets the identity component Theta_{v,0}.

        Here P.point is assumed to be a pair

            (x_P, y_P)

        of rational functions giving the coordinates of the section.
        """

        R = self.original_ring
        x,y,t = self.original_coords


        K = R.base_ring()

        Ru.<u> = PolynomialRing(K)

        phi = Ru.hom([t], R)
        
        if self.dynkin_labels is None:
            raise ValueError("Please first compute self.dynkin_labeling(cartan_type)")

        labels = self.dynkin_labels
        r = len(labels)

        v = vector(ZZ, r)
        coords = P.point

        if coords == (0,0):
            return v

        xP = coords[0]
        yP = coords[1]

        if self.is_infinity:

            Ku = Ru.fraction_field()

            def coordinate_at_infinity(f, weight):
                """
                f(t) -> u^weight f(1/u)
                """

                fn = f.numerator()
                fd = f.denominator()

                Rt = fn.parent()

                inv_map = Rt.hom(
                    [Ku(1) / Ku(u)],
                    Ku
                )

                return (
                    Ku(u**weight)
                    * inv_map(fn)
                    / inv_map(fd)
                )

            xP = coordinate_at_infinity(
                xP,
                2*self.infinity_chi
            )

            yP = coordinate_at_infinity(
                yP,
                3*self.infinity_chi
            )


        x_n0 = Ru(xP.numerator())
        x_d0 = Ru(xP.denominator())

        y_n0 = Ru(yP.numerator())
        y_d0 = Ru(yP.denominator())

        if x_d0(self.place) == 0 or y_d0(self.place) == 0: #NEEDS TO BE FIXED
            return v

        x_n = phi(x_n0)
        x_d = phi(x_d0)

        y_n = phi(y_n0)
        y_d = phi(y_d0)


        I_P = R.ideal([x_d*x - x_n, y_d*y - y_n])

        
        r_blowups = [
            self.blowups[blowup_id]
            for blowup_id in self.root.blowups
        ]

        if len(r_blowups) != 1:
            raise RuntimeError(
                "Currently only implemented for a Resolution object "
                "resolving one singular point."
            )

        first_step = r_blowups[0]

        # If P does not pass through the singular point at all,
        # then P meets Theta_{v,0}.
        if not self.ideal_contains_point(
            I_P,
            self.root,
            first_step.center
        ):
            return v

        section_ideals = {
            self.root.id: I_P
        }

        def section_ideal_on_chart(chart_id):

            if chart_id in section_ideals:
                return section_ideals[chart_id]

            chart = self.charts[chart_id]

            parent_I = section_ideal_on_chart(
                chart.parent_chart_id
            )

            I = self.strict_transform_ideal(
                parent_I,
                chart.parent_map,
                chart.exceptional_variable,
                chart.ring
            )

            section_ideals[chart_id] = I

            return I


        hit_steps = []

        for blowup_id, step in self.blowups.items():

            parent = self.charts[
                step.parent_chart_id
            ]

            I_section = section_ideal_on_chart(
                step.parent_chart_id
            )

            if self.ideal_contains_point(
                I_section,
                parent,
                step.center
            ):
                hit_steps.append(blowup_id)


        if len(hit_steps) == 0:
            return v

        def blowup_depth(blowup_id):

            step = self.blowups[blowup_id]

            parent = self.charts[
                step.parent_chart_id
            ]

            return len(parent.path)

        max_depth = max(
            blowup_depth(blowup_id)
            for blowup_id in hit_steps
        )

        deepest_hits = [
            blowup_id
            for blowup_id in hit_steps
            if blowup_depth(blowup_id) == max_depth
        ]

        if len(deepest_hits) != 1:
            raise RuntimeError(
                "Section passes through multiple deepest blowup centers: "
                f"{deepest_hits}"
            )

        last_blowup_id = deepest_hits[0]
        last_step = self.blowups[last_blowup_id]

        new_components = last_step.new_components

        if len(new_components) == 0:
            raise RuntimeError(
                f"Blowup {last_blowup_id} created no exceptional components."
            )

        if len(new_components) == 1:

            component_id = new_components[0]


        else:

            candidates = set()

            for child_id in last_step.children.values():

                child = self.charts[child_id]

                I_section = section_ideal_on_chart(
                    child_id
                )

                if I_section == child.ring.ideal(1):
                    continue

                for component_id in new_components:

                    if component_id not in child.component_patches:
                        continue

                    I_theta = child.component_patches[
                        component_id
                    ]

                    J = (
                        I_section
                        + I_theta
                        + child.ring.ideal([child.equation])
                    )

                    if child.ring.one() not in J:
                        candidates.add(component_id)

            if len(candidates) != 1:
                raise RuntimeError(
                    "Could not uniquely determine the exceptional "
                    "component met by the section after its final blowup. "
                    f"Candidates: {sorted(candidates)}"
                )

            component_id = candidates.pop()

        if component_id not in labels:
            raise RuntimeError(
                f"Component {component_id} is absent from the "
                "Dynkin labeling."
            )

        i = labels[component_id]

        v[i - 1] = 1

        return v

    def old_section_intersection(self, P):
        """
        Returns a tuple (P \cdot \Theta_{v,1}, \dots, P \cdot \Theta_{v,m_v - 1}) in the ordering aggreeing with SAGE's Cartan Matrix numbering.
        If the entire thing is 0, then it means P intersects \Theta_{v,0}
        """
        R = self.original_ring
        x,y,t = self.original_coords


        K = R.base_ring()

        Ru.<u> = PolynomialRing(K)

        phi = Ru.hom([t], R)
        
        if self.dynkin_labels is None:
            raise ValueError("Please first compute self.dynkin_labeling(cartan_type)")

        labels = self.dynkin_labels
        r = len(labels)

        v = vector(ZZ, r)
        coords = P.point

        if coords == (0,0):
            return v

        xP = coords[0]
        yP = coords[1]

        x_n0 = Ru(xP.numerator())
        x_d0 = Ru(xP.denominator())

        y_n0 = Ru(yP.numerator())
        y_d0 = Ru(yP.denominator())

        if x_d0(self.place) == 0 or y_d0(self.place) == 0: #I highly doubt this is right...
            return v

        x_n = phi(x_n0)
        x_d = phi(x_d0)

        y_n = phi(y_n0)
        y_d = phi(y_d0)


        I_P = R.ideal([x_d*x - x_n, y_d*y - y_n])

        r_blowups = [self.blowups[blowup_id] for blowup_id in self.root.blowups]

        if len(r_blowups) != 1:
            raise RuntimeError("Currently only implemented for object to have a blowup at one singular point, if more just create new object")

        first_step = r_blowups[0]

        if not self.ideal_contains_point(I_P, self.root, first_step.center):
            return v

        section_ideals = {self.root.id: I_P}

        def section_ideal_on_chart(chart_id):
            if chart_id in section_ideals:
                return section_ideals[chart_id]

            chart = self.charts[chart_id]

            parent_I = section_ideal_on_chart(chart.parent_chart_id)

            I = self.strict_transform_ideal(parent_I, chart.parent_map, chart.exceptional_variable, chart.ring)

            section_ideals[chart_id] = I

            return I

        '''print("\n===== BLOWUPS HIT BY SECTION =====")'''

        hit_steps = []

        for blowup_id, step in self.blowups.items():

            chart = self.charts[step.parent_chart_id]

            I_section = section_ideal_on_chart(
                step.parent_chart_id
            )

            hit = self.ideal_contains_point(
                I_section,
                chart,
                step.center
            )

            '''print(
                "blowup =", blowup_id,
                "chart =", step.parent_chart_id,
                "depth =", len(chart.path),
                "center =", step.center,
                "new =", step.new_components,
                "HIT =", hit
            )'''

            if hit:
                hit_steps.append(blowup_id)
        for chart_id in self.leaf_chart_ids():
            chart = self.charts[chart_id]
            I_section = section_ideal_on_chart(chart_id)

            for component_id, I_theta in chart.component_patches.items():

                K = I_section + I_theta + chart.ring.ideal([chart.equation])

                if chart.ring.one() in K:
                    continue

                '''print("\nCANDIDATE INTERSECTION")
                print("chart:", chart_id)
                print("path:", chart.path)
                print("component_id:", component_id)
                print("Dynkin label:", labels[component_id])
                print(
                    "skipped duplicate points:",
                    self.skipped_duplicate_points.get(chart_id, [])
                )'''

                stale = False

                for q in self.skipped_duplicate_points.get(chart_id, []):
                    '''print("testing stale point:", q)
                    print(
                        "  section contains:",
                        self.ideal_contains_point(I_section, chart, q)
                    )
                    print(
                        "  component contains:",
                        self.ideal_contains_point(I_theta, chart, q)
                    )'''

                    if (
                        self.ideal_contains_point(I_section, chart, q)
                        and self.ideal_contains_point(I_theta, chart, q)
                    ):
                        stale = True
                        break

                '''print("stale:", stale)'''

                if stale:
                    continue

                i = labels[component_id]
                v[i - 1] = 1
                return v

        '''for chart_id in self.leaf_chart_ids():
            chart = self.charts[chart_id]
            I_section = section_ideal_on_chart(chart_id)

            for component_id, I_theta in chart.component_patches.items():
                K = I_section + I_theta + chart.ring.ideal([chart.equation])

                if chart.ring.one() in K:
                    continue

                stale = False

                for q in self.skipped_duplicate_points.get(chart_id, []):
                    if (
                        self.ideal_contains_point(I_section, chart, q)
                        and self.ideal_contains_point(I_theta, chart, q)
                    ):
                        stale = True
                        break

                if stale:
                    continue

                if component_id not in labels:
                    raise RuntimeError(f"Component {component_id} occurs in chart {chart.id}, " "but is absent from the Dynkin labeling.")

                i = labels[component_id]

                v[i-1] = 1

                return v'''
        return v

    def correction_term(self, P, Q):
        """
        Computes contr_v(P,Q) on the singular fibre. Although there are tabulated values here, computing Cinv makes us consistent with the orderings in the whole program.
        """

        if self.dynkin_labels is None or self.cartan_type is None:
            raise ValueError("Please call self.dynkin_labelling(cartan_type) first")

        p = vector(QQ, self.section_intersection(P))
        q = vector(QQ, self.section_intersection(Q))

        if p.is_zero() or q.is_zero():
            return QQ(0)

        C = CartanMatrix(self.cartan_type)
        Cinv = C.inverse()

        return p.dot_product(Cinv * q)

    