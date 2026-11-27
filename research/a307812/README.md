# A307812 triangular digit products

There are 47 qualifying triangular numbers below 10³⁰⁰. All 46 greater than one are divisible by three. Exactly the triangular values 1 and 15 have digit product equal to their triangular index. Both unrestricted questions remain open. [OEIS A307812](https://oeis.org/A307812)

The OEIS table covers values below 10⁴⁹. The computation gives two further values within the larger range. The quotient in the last column is the product of the triangular number’s decimal digits divided by its triangular index. [Published table](https://oeis.org/A307812/b307812.txt)

| Triangular index | Triangular number | Quotient |
| ---: | ---: | ---: |
| 22627030279046045104078848 | 255991249624433272884692871488758547495385852542976 | 253125000 |
| 568674694735608432713269248 | 161695454216318718647597862769783644737279862427877376 | 559872000 |

For a qualifying value, its index divides a product of digits from 1 through 9. Every prime divisor of that index must therefore belong to {2, 3, 5, 7}. The search enumerates every such index up to the exact integer bound obtained from its triangular number. When the index is divisible by 20, the triangular number ends in zero. All other candidates undergo the decimal digit and divisibility checks directly.

Run `python research/a307812/search.py 300` for the triangular index, value, and quotient of each of the 47 terms. [Search code](search.py)
