from petlib.ec import EcGroup
from typing import List

class PolynomMod:

    @staticmethod
    def create_random_polynom(absolute_term, degree, q) -> 'PolynomMod':
        """
        Create a polynomial with random coefficients in range [1, q - 1] and an given absolute term.

        :param absolute_term: the absolute term (constant term)
        :param degree: the polynomial degree
        :param q: the modular order of the underlying group
        :return: the polynom
        """
        coefficients = [absolute_term]
        coefficients.extend([q.random() for _ in range(0, degree)])

        return PolynomMod(coefficients, q)

    def __init__(self, coefficients: List[int], q):
        # Make sure that the highest degree coefficient is set.
        # An alternative would be to strip trailing zero elements.
        assert coefficients[-1] != 0

        self.coefficients = coefficients
        self.q = q

    @property
    def degree(self) -> int:
        return len(self.coefficients) - 1

    def evaluate(self, x: int) -> int:
        """
        Evaluate the polynomial for a given x value.

        :param x: the value
        :return: the result
        """
        evaluated = ((self.coefficients[j] * pow(x, j)) for j in range(0, self.degree + 1))
        return sum(evaluated) % self.q

    def __str__(self) -> str:
        c_list = ["%d*x^%d " % (c, i) for (i, c) in enumerate(self.coefficients)]
        return "Polynom of degree {}: f(x) = {}".format(self.degree, " + ".join(c_list))

        
