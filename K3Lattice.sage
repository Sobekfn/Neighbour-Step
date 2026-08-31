from dataclasses import dataclass



@dataclass
class FibreBlock:
    cartan_type: tuple
    indices: tuple
    multiplicities: tuple
    intersection_matrix: object
    place: object
    point: tuple

@dataclass
class SectionBlock:
    index: tuple
    point: object #point on the elliptic surface W



def fibre_multiplicities(fibre_type, rank):
    L = CartanType([fibre_type, rank, 1])
    a = L.a()

    return tuple(ZZ(a[i]) for i in range(1, rank + 1))



class EllipticNS:
    def __init__(self, list_of_fibres, list_of_sections, basis_length):
        '''list_of_sections: List of NONTRIVIAL sections in the format of coordinates (x,y)
            list_of_fibres: List of reducible fibres in the format ['Type', 'rank'], (x,y) (ergo [[['A', 4], (0,0,0)], [['D', 7], (0,0,1)]] etc)
            basis_length: just length of basis of sublattice
        '''
        self.G = None
        self.rank = basis_length

        self.f = self.basis_vector(0)
        self.O = self.basis_vector(1)

        self.fibres = []

        start = 2

        for fibre, point in list_of_fibres:
            fibre_type = fibre[0]
            rank = Integer(fibre[1])

            indices = tuple(range(start, start + rank))

            multiplicities = fibre_multiplicities(fibre_type,rank)

            self.fibres.append(FibreBlock(
                cartan_type=(fibre_type, rank), 
                indices = indices, 
                multiplicities = multiplicities, 
                intersection_matrix= -CartanMatrix([fibre_type, rank]), 
                place=point[2], 
                point=(point[0], point[1])))

            start += rank

        self.sections = []
        for section in list_of_sections:
            S = SectionBlock(start, section)
            self.sections.append(S)
            start += 1
        


    def basis_vector(self, i):
        v = [0]*self.rank
        v[i] = 1
        return vector(ZZ, v)

    def zero_vector(self):
        return vector(ZZ, [0] * self.rank)

    def product(self, v, w):
        return (v * self.G).dot_product(w)

    def square(self, v):
        return self.product(v,v)

    def graph(self):
        """
        Intersection graph of the (-2)-curves currently known in NS.

        Includes:
            O,
            every fibre component Theta_{v,i}, including Theta_{v,0},
            every stored section.

        Vertices store the corresponding NS vector.
        """

        if self.G is None:
            raise ValueError(
                "Compute the NS intersection matrix first."
            )

        curves = {}

        # --------------------------------------------------------
        # O
        # --------------------------------------------------------

        curves["O"] = self.O

        # --------------------------------------------------------
        # Fibre components
        # --------------------------------------------------------

        for k, fibre in enumerate(self.fibres):

            # Theta_1,...,Theta_r
            thetas = []

            for j, index in enumerate(fibre.indices):

                theta = self.basis_vector(index)

                curves[
                    f"F{k}:Theta_{j+1}"
                ] = theta

                thetas.append(theta)

            # Theta_0 = F - sum m_i Theta_i
            theta0 = self.f.copy()

            for m, theta in zip(
                fibre.multiplicities,
                thetas
            ):
                theta0 -= m*theta

            curves[
                f"F{k}:Theta_0"
            ] = theta0

        # --------------------------------------------------------
        # Sections
        # --------------------------------------------------------

        for j, section in enumerate(self.sections):

            curves[
                f"P_{j+1}"
            ] = self.basis_vector(
                section.index
            )

        # --------------------------------------------------------
        # Graph
        # --------------------------------------------------------

        G = Graph()

        for name in curves:
            G.add_vertex(name)

        names = list(curves)

        for i in range(len(names)):
            for j in range(i + 1, len(names)):

                a = names[i]
                b = names[j]

                intersection = self.product(
                    curves[a],
                    curves[b]
                )

                if intersection != 0:
                    G.add_edge(
                        a,
                        b,
                        intersection
                    )

        return G, curves




