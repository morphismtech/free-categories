# free-categories

Consider the category of Haskell "quivers" with

* objects are types of higher kind
  * `p :: k -> k -> Type`
* morphisms are terms of `RankNType`,
  * `forall x y. p x y -> q x y`
* identity is `id`
* composition is `.`

Now, consider the subcategory of Haskell `Category`s with

* constrained objects `Category` `c => c`
* morphisms act functorially
  * `t :: (Category c, Category d) => c x y -> d x y`
  * `t id = id`
  * `t (g . f) = t g . t f`

The free category functor from quivers to `Category`s
may be defined up to isomorphism as

* the functor `Path` of type-aligned lists

* the functor `FoldPath` of categorical folds

* abstractly as `CFree` `path => path`, the class of
  left adjoints to the functor which
  forgets the constraint on `Category` `c => c`

* or as any isomorphic data structure
