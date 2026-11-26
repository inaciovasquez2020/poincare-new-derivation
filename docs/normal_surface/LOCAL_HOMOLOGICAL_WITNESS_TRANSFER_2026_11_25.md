# Local homological witnesses and geometric bridge

PROVED_ON_PAPER; no new Lean or global Poincare claim.

For finite-dimensional embedded local cycle subspaces U_v, d=dim(sum_v U_v) and D=max_v dim U_v>0, extract a basis from the union of local bases and assign each vector to a supporting center. Each center receives at most D independent vectors. Keeping one per center gives at least ceil(d/D) independent vectors with distinct centers. These need not have disjoint support, bound disks or correspond to legal moves. For a linear map gamma, use the dimension of the sum of image subspaces gamma(U_v) to obtain independent image witnesses; independence need not survive mapping.

The bounded-radius fundamental-cycle candidate fails on C_n (its only fundamental cycle has diameter floor(n/2)). Even connected 4-regular graphs do not suffice: C_n square K_3 is 4-regular for n>=4. Projection to C_n induces a surjection on F2 cycle spaces by a horizontal layer. For n>2R+1, a radius-R ball projects into a proper path of C_n, hence any cycle supported there has zero projected cycle vector. If all fundamental cycles were so supported they could not span a space surjecting onto the cycle space of C_n. Thus degree four alone does not imply bounded-radius generation. These graphs are not asserted to be dual graphs of simply connected triangulated 3-manifolds.

The remaining bridge requires actual manifold hypotheses, geometric disk boundaries generating the relevant image space, and legal move compatibility. Existing Pachner certificates are unchanged.
