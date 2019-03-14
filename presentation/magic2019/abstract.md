What manifolds are “pseudo-affine“? What numerics can be done on this abstraction?
===

The classical understanding of a manifold involves the notion of (in general,
multiple) charts. This makes it cumbersome to implement numerical algorithms
that would need to be able to explicitly switch between charts. Within each
chart however, there is the much simpler vector space structure to work with.
We demonstrate a Haskell type class that abstracts, somewhat naïvely, over the
process of chart-selecting. This interface is practically the same as that
of affine spaces, except that addition is in general not associative.

The thus selected chart-space for each point is isomorphic to the tangent space,
which gives a straightforward intuition for how numerical algorithms can be
implemented. We present a few examples doing this in the Haskell library,
including a mesh-generation prototype that works with no need for coordinates
nor a Riemannian structure.

The pseudo-affine formalism has suggestive similarity with the better studied one
of homogeneous spaces with Lie groups and -algebras, which are probably required
to rigorously extend this work to higher-order schemes.
