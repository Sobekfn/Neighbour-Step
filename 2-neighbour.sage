from itertools import combinations, combinations_with_replacement



INF = "infinity"

'''The main metho
INPUTS: W = current Weierstrass Model (i.e. EllipticCurve([a1,a2,a3,a4,a6]) over a field like QQ(r,s,u,v) or something like that)

E = Weierstrass Equation 

(MUST BE MINIMAL)

, NS = basis of Neron-Severi Lattice and Intersection Matirx, fprime = new elliptic divisor

I assume NS was built using K3Lattice.sage, and fprime is a vector given in terms of the basis of NS

'''

def compute_NS_gram_matrix(W, E, NS, n=2):

    F = NS.f

    resolution_list = {}

    correction_terms = {}
    correction_terms_2 = {}

    r = len(NS.sections)

    infinity_data = None

    for fibre in NS.fibres:

        v = fibre.place

        '''print(
            "Resolving fibre:",
            repr(v),
            "type:",
            type(v),
            flush=True
        )'''


        if v == "infinity":

            '''print("  -> using INFINITY branch", flush=True)'''

            if infinity_data is None:

                infinity_data = infinity_local_model(
                    E,
                    chi=n
                )

            E_inf, source_images = infinity_data

            Kinf = E_inf.parent().base_ring()


            q = (
                Kinf(fibre.point[0]),
                Kinf(fibre.point[1]),
                Kinf(0)
            )

            res = Resolution(
                E_inf,
                source_ring=E.parent(),
                source_images=source_images,
                infinity_chi=n
            )

            res.resolve(q)

        else:

            '''print("  -> using finite branch", flush=True)'''

            q = (
                fibre.point[0],
                fibre.point[1],
                v
            )

            res = Resolution(E)

            res.resolve(q)

        res.dynkin_labeling(
            [
                fibre.cartan_type[0],
                fibre.cartan_type[1]
            ]
        )

        resolution_list[v] = res

        #computing correction terms
        Contr = Matrix(QQ, r, r)
        Contr_2 = Matrix(QQ, r, r)


        for i,j in combinations_with_replacement(
            range(r),
            2
        ):

            c = res.correction_term(
                NS.sections[i],
                NS.sections[j]
            )

            Contr[i,j] = c
            Contr[j,i] = c


        for i,j in combinations_with_replacement(
            range(r),
            2
        ):

            P_i = W(
                NS.sections[i].point
            )

            P_j = W(
                NS.sections[j].point
            )

            Q = P_i + P_j

            Qblock = SectionBlock(
                index=None,
                point=(
                    Q[0],
                    Q[1]
                )
            )

            c = res.correction_term(
                Qblock,
                Qblock
            )

            Contr_2[i,j] = c
            Contr_2[j,i] = c


        correction_terms[v] = Contr
        correction_terms_2[v] = Contr_2



    H = height_pairing_matrix_builder(
        W,
        NS,
        correction_terms,
        correction_terms_2,
        n=n
    )


    C = Matrix(QQ, r, r)

    for i,j in combinations_with_replacement(
        range(r),
        2
    ):

        P_O = section_intersect_zero_section(
            NS.sections[i],
            n=n
        )

        Q_O = section_intersect_zero_section(
            NS.sections[j],
            n=n
        )

        contr = 0

        for fibre in NS.fibres:

            contr += correction_terms[
                fibre.place
            ][i,j]

        c = (
            n
            + P_O
            + Q_O
            - H[i,j]
            - contr
        )

        C[i,j] = c
        C[j,i] = c


    NS.G = intersection_matrix_builder(
        NS,
        resolution_list,
        C
    )

    return resolution_list

def two_neigbour(W, E, NS, Fprime, resolution_list, n=2):
    F = NS.f

    
    #As a sanity check , assert the following are true:
    
    assert NS.product(F, Fprime) == 2
    
    assert NS.square(F) == 0
    
    assert NS.square(Fprime) == 0 

    P = compute_P(W, NS, Fprime)

    V = compute_V(NS, Fprime, F, P, resolution_list)

    # Compute k and the actual divisor kF - V
    k, conditions = find_k_and_conditions(
        NS,
        V,
        resolution_list
    )

    # Proposition 2.17 + Remark 2.19
    H0 = apply_remark_219(
        E,
        NS,
        P,
        k,
        conditions,
        resolution_list
    )

    if len(H0) != 2:
        raise ArithmeticError(
            f"Expected dim H^0(Fprime) = 2 after Remark 2.19, "
            f"but obtained {len(H0)}."
        )

    phi0, phi1 = H0

    #new base parameter
    u = phi1 / phi0

    return u

    

def section_intersect_zero_section(P, n = 2):
    """
    Computes P \cdot O
    """
    xcoord = P.point[0]

    R = xcoord.parent()

    if R.is_integral_domain() and not R.is_field():
        xcoord = R.fraction_field()(xcoord)

    a = xcoord.numerator().degree()
    b = xcoord.denominator().degree()
    
    return max(b, a - 2*n)//2

def intersection_matrix_builder(NS, resolution_list, C):
    """
    returns the intersection matrix
    """

    #we first build the trivial lattice part:

    U = matrix(ZZ, [[0, 1], [1, -2]])
    blocks = [U]

    for fibre in NS.fibres:
        R = CartanMatrix([fibre.cartan_type[0], fibre.cartan_type[1]])
        blocks.append(-R)

    A = block_diagonal_matrix(blocks)

    n = A.nrows()

    G = block_diagonal_matrix([A,C])

    m = G.nrows()

    for i in range(n,m):
        G[0,i] = 1
        G[i,0] = 1 #every section meets each fibre exactly once

        P = NS.sections[i - n]

        l = section_intersect_zero_section(P)
        G[i,1] = l
        G[1,i] = l

        p = 2

        for fibre in NS.fibres:
            res = resolution_list[fibre.place]

            v = res.section_intersection(P)

            for j in range(len(v)):
                G[i,p] = v[j]
                G[p,i] = v[j]
                p+= 1
    return G

def height_pairing_matrix_builder(W, NS, C, C2, n=2):

    """
    Returns the height pairing matrix H with entires <P_i, P_j>
    """

    r = len(NS.sections)
    H = Matrix(QQ, r, r)

    #First we build the diagonal:
    for i in range(r):
        P = NS.sections[i]
        P_intersect_O = section_intersect_zero_section(P, n=n)

        S = 0
        for fibre in NS.fibres:
            S += C[fibre.place][i,i]
        H[i,i] = 2*n + 2*P_intersect_O - S



    #Now use the polarisation identity to fill out the rest:
    for i,j in combinations_with_replacement(range(r), 2):
        if i != j:
            #first need to compute h(P_i + P_j)
            P_i = W(NS.sections[i].point)
            P_j = W(NS.sections[j].point)

            Qsum = P_i + P_j

            Q = SectionBlock(index=None, point=(Qsum[0], Qsum[1]))

            Q_intersect_O = section_intersect_zero_section(Q, n=n)

            S = 0
            for fibre in NS.fibres:
                S += C2[fibre.place][i,j]

            h_ij = 2*n + 2*Q_intersect_O - S


            height = QQ(1)/2*(h_ij - H[i,i] - H[j,j])

            H[i,j] = height
            H[j,i] = height
    return H
    

def singular_point(v, A, B, C, K0):

        v = K0(v)

        vals = [
            K0(A(v)),
            K0(B(v)),
            K0(C(v))
        ]

        for i in range(3):
            for j in range(i + 1, 3):

                if vals[i] == vals[j]:

                    return (
                        -vals[i],
                        K0(0),
                        v
                    )

        raise ArithmeticError(
            f"No repeated root at t = {v}"
        )

def compute_P(W, NS, Fprime):
    P = W(0)

    for section in NS.sections:
        n = ZZ(Fprime[section.index])

        if n != 0:
            P += n*W(section.point)

    if P == W(0):
        return None

    return SectionBlock(
        index=None,
        point=(P[0], P[1])
    )


def compute_V(NS, Fprime, F, P, resolution_list, chi=2):
    d = NS.product(Fprime, F)
    DO = NS.product(Fprime, NS.O)

    if P is None:
        # P = O, so P.O = O^2 = -chi
        PO = -chi
    else:
        PO = section_intersect_zero_section(
            P,
            n=chi
        )

    n = (d - 1)*chi + DO - PO

    V = vector(ZZ, [0]*NS.rank)
    V[0] = ZZ(n)

    p = 2

    for fibre in NS.fibres:
        Av = -CartanMatrix(
            fibre.cartan_type
        )

        Avinv = Av.inverse()

        r = Av.nrows()

        D = Matrix(
            QQ,
            r,
            1
        )

        res = resolution_list[
            fibre.place
        ]

        if P is None:
            # O meets Theta_0, hence none of the
            # nonidentity components.
            L = vector(ZZ, [0]*r)
        else:
            L = res.section_intersection(P)

        for i in range(r):
            Theta = vector(
                ZZ,
                [0]*NS.rank
            )

            Theta[p+i] = 1

            D[i,0] = (
                NS.product(
                    Fprime,
                    Theta
                )
                - L[i]
            )

        B = Avinv * D

        for i in range(r):
            b = B[i,0]

            if b not in ZZ:
                raise ArithmeticError(
                    f"Nonintegral coefficient of V "
                    f"at fibre {fibre.place}: {b}"
                )

            V[p+i] = ZZ(b)

        p += r

    return V


def compute_basis_zero(E, k, pole_place = QQ(1)):
    """
    Basis of H^0(2O + kF), with F = {T=1}. (THIS NEEDS TO BE FIXED!!)

    Functions have the form

        (a(T) + b(T)X) / T^k

    with
        deg(a) <= k,
        deg(b) <= k-4.
    """

    S = E.parent()
    X, Y, T = S.gens()

    q = T - pole_place

    K = S.fraction_field()

    basis = []

    for i in range(k + 1):
        basis.append(
            K(T^i) / K(q^k)
        )

    for i in range(max(0, k - 3)):
        basis.append(
            K(T^i * X) / K(q^k)
        )

    return basis


def apply_remark_219(
    E,
    NS,
    P,
    k,
    conditions,
    resolution_list
):
    R = E.parent()
    X, Y, T = R.gens()

    if P is None:
        basis = compute_basis_zero(
            E,
            k
        )

    else:
        ab_basis = compute_basis(
            P,
            k
        )

        basis = [
            build_easy_section(
                a,
                b,
                P,
                k,
                X,
                Y
            )
            for a,b in ab_basis
        ]

    current_basis = basis

    for fibre in NS.fibres:
        data = conditions[
            fibre.place
        ]

        res = resolution_list[
            fibre.place
        ]

        current_basis = (
            res.impose_vertical_conditions(
                current_basis,
                identity_order=
                    data["identity_order"],
                exceptional_orders=
                    data["exceptional_orders"]
            )
        )

        if len(current_basis) == 0:
            raise ArithmeticError(
                "Remark 2.19 killed the entire "
                f"linear system at fibre "
                f"{fibre.place}."
            )

    return current_basis

def old_compute_P(W, NS, Fprime):
    P = W(0)

    for section in NS.sections:
        n = ZZ(Fprime[section.index])

        if n != 0:
            P += n*W(section.point)

    return SectionBlock(index=None, point=(P[0], P[1]))

def old_compute_V(NS, Fprime, F, P, resolution_list, chi=2):
    #Look at Lemma 2.5. and 5.1. in Shioda for why we do the way we do this:
    d = NS.product(Fprime, F)
    DO = NS.product(Fprime, NS.O)
    PO = section_intersect_zero_section(P, n=chi)

    n = (d-1)*chi + DO - PO

    V = vector(ZZ, [0]*NS.rank)

    V[0] = n

    p = 2

    for fibre in NS.fibres:
        Av = -CartanMatrix(fibre.cartan_type)
        Avinv = Av.inverse()

        r = Avinv.nrows()
        D = Matrix(QQ, r, 1) #will be the other multiplicant

        res = resolution_list[fibre.place]

        L = res.section_intersection(P)

        for i in range(p, p + r):
            Theta_vi = vector(ZZ, [0]*NS.rank)
            Theta_vi[i] = 1
            D[i-p, 0] = NS.product(Fprime, Theta_vi) - L[i-p]

        B = Avinv*D

        for i in range(p, p+r):
            V[i] = ZZ(B[i-p,0])

        p = p+r

    return V

def compute_basis(P, k, OP=None, n=2):
    """
    Compute the pair (a(t), b(t)) mentioned in Proposition 2.17. in Elkies-Brandhorst paper on the K3 Lehmer map
    """
    Q = P.point
    xP = Q[0]
    yP = Q[1]

    xn = xP.numerator()
    xd = xP.denominator()
    yn = yP.numerator()
    yd = yP.denominator()

    R = xd.parent()
    K = R.base_ring()

    t = R.gen()

    dx = xd.degree()
    dxn = xn.degree()
    if OP is None:
        two_OP = max(dx, dxn - 2*n)

        if two_OP % 2 != 0:
            raise ArithmeticError(
                "Formula for 2(O.P) gave an odd integer."
            )

        OP = ZZ(two_OP // 2)

    A = 2*OP + k

    if dx % 2 != 0:
        raise ValueError("deg(x_d) should be even.")

    B = k + 2*OP - 2 - dx//2

    C = k + 2*OP + 4 + dx

    na = A + 1 #upper bound on num of coefficients in the a poly

    # If B < 0, then b = 0
    nb = max(0, B + 1) #upper bound on num of coefficients in the b poly

    nvars = na + nb #num of total unknown variables

    #let q = ax_n - dy_n = a \sum

    q_columns = []

    for i in range(na):
        q_columns.append(t^i * xn)

    for i in range(nb):
        q_columns.append(-t**i * yn)

    rows = []

    #we need to impose q = 0 mod x_d

    if dx > 0:
        remainders = [q.quo_rem(xd)[1] for q in q_columns]

        for l in range(dx):
            rows.append([r[l] for r in remainders])

    #(3): deg q <= C
    nonzero_q = [q for q in q_columns if q != 0]

    if nonzero_q: 
        max_degree = max(q.degree() for q in nonzero_q)

        for l in range(C + 1, max_degree + 1):
            rows.append([q[l] for q in q_columns])

    if rows:
        M = Matrix(K, rows)
    else:
        M = Matrix(K, 0, nvars)

    ker = M.right_kernel()

    basis = []

    for v in ker.basis():

        a = R.zero()
        b = R.zero()

        for i in range(na):
            a += v[i] * t**i

        for j in range(nb):
            b += v[na + j] * t**j

        basis.append((a, b))

    expected_dimension = 2*k + OP

    if len(basis) != expected_dimension:
        raise ArithmeticError(
            f"Proposition 2.17 dimension check failed: "
            f"computed {len(basis)}, expected {expected_dimension}."
        )

    return basis

def find_k_and_conditions(NS, V, resolution_list):
    n = ZZ(V[0])
    k = n
    p = 2
    conditions = {}

    for fibre in NS.fibres:
        res = resolution_list[fibre.place]
        r = CartanMatrix(fibre.cartan_type).nrows()
        m = list(fibre.multiplicities)

        if len(m) == r + 1:
            m = m[1:]
        elif len(m) != r:
            raise ValueError(
                f"Unexpected multiplicity vector at fibre {fibre.place}: {fibre.multiplicities}"
            )

        b = [ZZ(V[p + i]) for i in range(r)]

        k_v = ZZ(0)
        for i in range(r):
            k_v = max(k_v, ZZ(ceil(QQ(b[i]) / QQ(m[i]))))

        k_v = max(ZZ(0), k_v)
        k += k_v

        component_from_label = {
            label: component_id
            for component_id, label in res.dynkin_labels.items()
        }

        exceptional_orders = {}

        for i in range(r):
            label = i + 1
            order = ZZ(k_v*m[i] - b[i])

            if order < 0:
                raise ArithmeticError(
                    f"Negative Remark 2.19 multiplicity at fibre "
                    f"{fibre.place}, component {label}: {order}"
                )

            if order == 0:
                continue

            if label not in component_from_label:
                raise RuntimeError(
                    f"No resolution component with Dynkin label {label}"
                )

            exceptional_orders[component_from_label[label]] = order

        conditions[fibre.place] = {
            "identity_order": k_v,
            "exceptional_orders": exceptional_orders
        }

        p += r

    return k, conditions

def build_easy_section(a, b, P, k, X, Y):
    xP, yP = P.point

    xn = xP.numerator()
    xd = xP.denominator()
    yn = yP.numerator()
    yd = yP.denominator()

    Rt = xd.parent()
    S = X.parent()
    T = S.gens()[2]

    phi = Rt.hom([T], S)

    a = phi(a)
    b = phi(b)
    xn = phi(xn)
    xd = phi(xd)
    yn = phi(yn)
    yd = phi(yd)

    numerator = a*(X*xd - xn) + b*(Y*yd + yn)
    denominator = T**k * xd * (X*xd - xn)

    K = S.fraction_field()
    return K(numerator) / K(denominator)



def infinity_local_model(E, chi=2):
    r"""
    Construct the local Weierstrass chart at t = infinity.

    Global coordinates:
        (x,y,t)

    Local coordinates:
        s = 1/t
        X = s^(2 chi) x
        Y = s^(3 chi) y

    For a K3, chi=2:
        X = s^4 x
        Y = s^6 y.
    """

    R = E.parent()
    x, y, t = R.gens()

    K = R.base_ring()

    S = PolynomialRing(
        K,
        names=("Xinf", "Yinf", "s")
    )

    Xinf, Yinf, s = S.gens()

    KS = S.fraction_field()

    # Global coordinate functions written in the local chart
    source_images = (
        KS(Xinf) / KS(s)**(2*chi),
        KS(Yinf) / KS(s)**(3*chi),
        KS(1) / KS(s)
    )

    global_to_inf = R.hom(
        list(source_images),
        KS
    )

    # Every term of a Weierstrass equation has weight 6 chi.
    E_rat = (
        KS(s)**(6*chi)
        * global_to_inf(E)
    )

    # It should now be polynomial for a global minimal weierstrass model
    den = S(E_rat.denominator())

    if not den.is_unit():
        raise ArithmeticError(
            "The infinity transformation did not produce "
            "a polynomial equation. Is the global "
            "Weierstrass model minimal?"
        )

    E_inf = S(
        E_rat.numerator() / den
    )

    return (
        E_inf,
        source_images
    )
