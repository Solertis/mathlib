/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import topology.category.Top.basic
import category_theory.limits.types
import category_theory.limits.preserves.basic

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

open topological_space
open category_theory
open category_theory.limits
open opposite

universes u v

noncomputable theory

namespace Top

variables {J : Type u} [small_category J]

local notation `forget` := forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{u}) : cone F :=
{ X := Top.of {u : Π j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j},
  π :=
  { app := λ j,
    { to_fun := λ u, u.val j,
      continuous_to_fun := show continuous ((λ u : Π j : J, F.obj j, u j) ∘ subtype.val),
        by continuity } } }

/--
A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone_infi (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨(types.limit_cone (F ⋙ forget)).X, ⨅j,
        (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
  π :=
  { app := λ j, ⟨(types.limit_cone (F ⋙ forget)).π.app j,
                 continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f,
                   continuous_map.coe_inj ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone F) :=
{ lift := λ S, { to_fun := λ x, ⟨λ j, S.π.app _ x, λ i j f, by { dsimp, erw ← S.w f, refl }⟩ },
  uniq' := λ S m h, by { ext : 3, simpa [← h] } }

/--
The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_infi_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone_infi F) :=
by { refine is_limit.of_faithful forget (types.limit_cone_is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.π.app j).continuous :
         _) ) }

instance Top_has_limits : has_limits.{u} Top.{u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) } }

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨(types.colimit_cocone (F ⋙ forget)).X, ⨆ j,
        (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
  ι :=
  { app := λ j, ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j,
                 continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f,
                   continuous_map.coe_inj ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit_cocone F) :=
by { refine is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (λ s, ⟨_, _⟩)
       (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.ι.app j).continuous :
         _) ) }

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk { cocone := colimit_cocone F, is_colimit :=
    colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

end Top

namespace Top

section cofiltered_limit

variables {J : Type u} [small_category J] [is_cofiltered J] (F : J ⥤ Top.{u})
  (C : cone F) (hC : is_limit C)

include hC

/--
Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit
  (T : Π j, set (set (F.obj j))) (hT : ∀ j, is_topological_basis (T j))
  (univ : ∀ (i : J), set.univ ∈ T i)
  (inter : ∀ i (U1 U2 : set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
  (compat : ∀ (i j : J) (f : i ⟶ j) (V : set (F.obj j)) (hV : V ∈ T j), (F.map f) ⁻¹' V ∈ T i) :
  is_topological_basis { U : set C.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } :=
begin
  classical,
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limit_cone_infi F,
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _),
  have hE : inducing E.hom := (Top.homeo_of_iso E).inducing,
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices : is_topological_basis
    { U : set D.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V },
  { convert this.inducing hE,
    ext U0,
    split,
    { rintro ⟨j, V, hV, rfl⟩,
      refine ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩ },
    { rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩,
      refine ⟨j, V, hV, rfl⟩ } },
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert is_topological_basis_infi hT (λ j (x : D.X), D.π.app j x),
  ext U0,
  split,
  { rintros  ⟨j, V, hV, rfl⟩,
    let U : Π i, set (F.obj i) := λ i, if h : i = j then (by {rw h, exact V}) else set.univ,
    refine ⟨U,{j},_,_⟩,
    { rintro i h,
      rw finset.mem_singleton at h,
      dsimp [U],
      rw dif_pos h,
      subst h,
      exact hV },
    { dsimp [U],
      simp } },
  { rintros ⟨U, G, h1, h2⟩,
    obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G,
    let g : ∀ e (he : e ∈ G), j ⟶ e := λ _ he, (hj he).some,
    let Vs : J → set (F.obj j) := λ e, if h : e ∈ G then F.map (g e h) ⁻¹' (U e) else set.univ,
    let V : set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e,
    refine ⟨j, V, _, _⟩,
    { -- An intermediate claim used to apply induction along `G : finset J` later on.
      have : ∀ (S : set (set (F.obj j))) (E : finset J) (P : J → set (F.obj j))
        (univ : set.univ ∈ S)
        (inter : ∀ A B : set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
        (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S), (⋂ e (he : e ∈ E), P e) ∈ S,
      { intros S E,
        apply E.induction_on,
        { intros P he hh,
          simpa },
        { intros a E ha hh1 hh2 hh3 hh4 hh5,
          rw finset.set_bInter_insert,
          refine hh4 _ _ (hh5 _ (finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _),
          intros e he,
          exact hh5 e (finset.mem_insert_of_mem he) } },
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine this _ _ _ (univ _) (inter _) _,
      intros e he,
      dsimp [Vs],
      rw dif_pos he,
      exact compat j e (g e he) (U e) (h1 e he), },
    { -- conclude...
      rw h2,
      dsimp [V],
      rw set.preimage_Inter,
      congr' 1,
      ext1 e,
      rw set.preimage_Inter,
      congr' 1,
      ext1 he,
      dsimp [Vs],
      rw [dif_pos he, ← set.preimage_comp],
      congr' 1,
      change _ = ⇑(D.π.app j ≫ F.map (g e he)),
      rw D.w } }
end

end cofiltered_limit

section topological_konig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

TODO: The theorem hold also in the case `{J : Type u} [category J] [is_cofiltered J]`.
See https://stacks.math.columbia.edu/tag/086J for the Set version and
See https://stacks.math.columbia.edu/tag/0032 for how to lift this to general cofiltered categories
rather than thin ones.
-/

variables {J : Type u} [small_category J] [is_cofiltered J]
variables (F : J ⥤ Top.{u})

/--
The partial sections of an inverse system of topological spaces from an index `j` are sections
when restricted to all objects less than or equal to `j`.
-/
def partial_sections {G : finset J} (H : finset (Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y)) :
  set (Π j, F.obj j) :=
{ u | ∀ {f : (Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y)} (hf : f ∈ H),
  F.map f.2.2.2.2 (u f.1) = u f.2.1 }

lemma partial_sections.nonempty [h : Π (j : J), nonempty (F.obj j)]
  {G : finset J} (H : finset (Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y)) :
  (partial_sections F H).nonempty :=
begin
  classical,
  let j0 := is_cofiltered.inf G H,
  let fs : ∀ {X : J}, X ∈ G → (j0 ⟶ X) := λ X hX, is_cofiltered.inf_to G H hX,
  have hfs := @is_cofiltered.inf_to_commutes _ _ _ G H,
  let x0 := (h j0).some,
  let u : Π j, F.obj j := λ j, if hj : j ∈ G then F.map (fs hj) x0 else (h _).some,
  use u,
  rintros ⟨X,Y,hX,hY,f⟩ hf,
  dsimp only [u],
  rw dif_pos hX,
  rw dif_pos hY,
  rw [← comp_app, ← F.map_comp],
  rwa hfs,
end

lemma partial_sections.closed [Π (j : J), t2_space (F.obj j)]
  {G : finset J} (H : finset (Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y)) :
  is_closed (partial_sections F H) :=
begin
  have : partial_sections F H = ⋂ {f : (Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y)} (hf : f ∈ H),
    { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 } := by tidy,
  rw this,
  apply is_closed_bInter,
  intros f hf,
  apply is_closed_eq,
  continuity,
end

lemma nonempty_limit_cone_of_compact_t2_inverse_system
  [Π (j : J), nonempty (F.obj j)]
  [Π (j : J), compact_space (F.obj j)]
  [Π (j : J), t2_space (F.obj j)] :
  nonempty (Top.limit_cone F).X :=
begin
  classical,
  let PP := Σ (G : finset J),  finset (Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y),
  have := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ G : PP, partial_sections F G.2) _ _ _ _,
  { obtain ⟨u,hu⟩ := this,
    use u,
    intros X Y f,
    let G : PP := ⟨{X,Y},{⟨X,Y,by simp, by simp, f⟩}⟩,
    exact hu _ ⟨G,rfl⟩ (finset.mem_singleton_self _) },
  { intros A B,
    let ιA : (Σ' (X Y : J) (mX : X ∈ A.1) (mY : Y ∈ A.1), X ⟶ Y) →
      (Σ' (X Y : J) (mX : X ∈ A.1 ⊔ B.1) (mY : Y ∈ A.1 ⊔ B.1), X ⟶ Y) :=
      λ f, ⟨f.1, f.2.1, _, _, f.2.2.2.2⟩,
    rotate,
    { apply finset.mem_union_left,
      exact f.2.2.1 },
    { apply finset.mem_union_left,
      exact f.2.2.2.1 },
    let ιB : (Σ' (X Y : J) (mX : X ∈ B.1) (mY : Y ∈ B.1), X ⟶ Y) →
      (Σ' (X Y : J) (mX : X ∈ A.1 ⊔ B.1) (mY : Y ∈ A.1 ⊔ B.1), X ⟶ Y) :=
      λ f, ⟨f.1, f.2.1, _, _, f.2.2.2.2⟩,
    rotate,
    { apply finset.mem_union_right,
      exact f.2.2.1 },
    { apply finset.mem_union_right,
      exact f.2.2.2.1 },
    refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩,_,_⟩,
    { rintro u hu f hf,
      have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB,
      { apply finset.mem_union_left,
        rw finset.mem_image,
        refine ⟨f, hf, rfl⟩ },
      exact hu this },
    { rintro u hu f hf,
      have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB,
      { apply finset.mem_union_right,
        rw finset.mem_image,
        refine ⟨f, hf, rfl⟩ },
      exact hu this } },
  { intros G,
    apply partial_sections.nonempty },
  { intros G,
    apply is_closed.is_compact,
    apply partial_sections.closed },
  { intros G,
    apply partial_sections.closed },
end

end topological_konig

end Top

section fintype_konig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
lemma nonempty_sections_of_fintype_inverse_system.init
  {J : Type u} [small_category J] [is_cofiltered J] (F : J ⥤ Type u)
  [hf : Π (j : J), fintype (F.obj j)] [hne : Π (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  let F' : J ⥤ Top := F ⋙ Top.discrete,
  haveI : Π (j : J), fintype (F'.obj j) := hf,
  haveI : Π (j : J), nonempty (F'.obj j) := hne,
  obtain ⟨⟨u, hu⟩⟩ := Top.nonempty_limit_cone_of_compact_t2_inverse_system F',
  exact ⟨u, λ _ _ f, hu f⟩,
end

-- I'm fairly sure we have something like this somewhere...
instance ulift.small_category (α : Type u) [small_category α] [is_cofiltered α] :
  small_category (ulift.{v} α) :=
{ hom := λ X Y, ulift (X.down ⟶ Y.down),
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.down ≫ g.down⟩ }

-- This should move.
instance ulift.is_cofiltered (α : Type u) [small_category α] [is_cofiltered α] :
  is_cofiltered (ulift.{v} α) :=
{ cocone_objs := λ X Y, ⟨⟨is_cofiltered.min X.down Y.down⟩, ⟨is_cofiltered.min_to_left _ _⟩,
    ⟨is_cofiltered.min_to_right _ _⟩, trivial⟩,
  cocone_maps := λ X Y f g, ⟨⟨is_cofiltered.eq f.down g.down⟩,
    ⟨is_cofiltered.eq_hom _ _⟩, by { ext, apply is_cofiltered.eq_condition }⟩,
  nonempty := ⟨⟨is_cofiltered.nonempty.some⟩⟩ }

/-- The inverse limit of nonempty finite types is nonempty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `J` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_fintype_inverse_system
  {J : Type u} [small_category J] [is_cofiltered J] (F : J ⥤ Type v)
  [Π (j : J), fintype (F.obj j)] [Π (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  -- Step 1: lift everything to the `max u v` universe.
  let J' := ulift.{v} J,
  let down : J' ⥤ J :=
  { obj := ulift.down,
    map := λ i j f, f.down },
  let tu : Type v ⥤ Type (max u v) := ulift_functor.{u v},
  let F' : (ulift.{v} J) ⥤ Type (max u v) := down ⋙ F ⋙ tu,
  haveI : ∀ i, nonempty (F'.obj i) := λ i,
    ⟨ulift.up (classical.arbitrary (F.obj i.down))⟩,
  haveI : ∀ i, fintype (F'.obj i) := λ i,
    fintype.of_equiv (F.obj i.down) equiv.ulift.symm,
  -- Step 2: apply the bootstrap theorem
  obtain ⟨u, hu⟩ := nonempty_sections_of_fintype_inverse_system.init F',
  -- Step 3: interpret the results
  use λ j, (u (ulift.up j)).down,
  intros j j' f,
  let f' : ulift.up.{v} j ⟶ ulift.up.{v} j' := ⟨f⟩,
  have h := hu f',
  simp only [functor.comp_map, ulift_functor_map, functor.op_map] at h,
  simp only [←h],
end

end fintype_konig
