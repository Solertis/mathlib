/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import data.matrix.notation
import linear_algebra.char_poly.coeff
import linear_algebra.determinant
-- import ring_theory.dedekind_domain
-- import ring_theory.fractional_ideal
import ring_theory.localization
import ring_theory.power_basis

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/

universes u v w

variables {R S T : Type*} [integral_domain R] [integral_domain S] [integral_domain T]
variables [algebra R S] [algebra R T]
variables {K L F : Type*} [field K] [field L] [field F]
variables [algebra K L] [algebra L F] [algebra K F]
variables {ι : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix
open ring

open_locale big_operators
open_locale matrix

namespace algebra

variables (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
linear_map.det.comp (lmul R S).to_ring_hom.to_monoid_hom

@[simp] lemma norm_apply (x : S) : norm R x = linear_map.det (lmul R S x) := rfl

variables {S}

lemma norm_eq_one_of_not_exists_basis
  (h : ¬ ∃ (s : finset S), nonempty (basis s R S)) (x : S) : norm R x = 1 :=
by { rw [norm_apply, linear_map.det], split_ifs with h, refl }

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma norm_eq_matrix_det [decidable_eq ι] (b : basis ι R S) (s : S) :
  norm R s = matrix.det (algebra.left_mul_matrix b s) :=
by rw [norm_apply, ← linear_map.det_to_matrix b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
lemma norm_algebra_map_of_basis (b : basis ι R S) (x : R) :
  norm R (algebra_map R S x) = x ^ fintype.card ι :=
begin
  haveI := classical.dec_eq ι,
  rw [norm_apply, ← det_to_matrix b, lmul_algebra_map],
  convert @det_diagonal _ _ _ _ _ (λ (i : ι), x),
  { ext i j, rw [to_matrix_lsmul, matrix.diagonal] },
  { rw [finset.prod_const, finset.card_univ] }
end

lemma basis.nonempty_index {ι R M : Type*} [semiring R] [add_comm_monoid M] [module R M]
  (b : basis ι R M) [nontrivial M] : nonempty ι :=
begin
  obtain ⟨x, hx⟩ := exists_ne (0 : M),
  have := b.repr.injective.ne hx,
  contrapose! this,
  ext i,
  have : nonempty ι := ⟨i⟩,
  contradiction
end

lemma basis.card_pos {R M : Type*} [semiring R] [add_comm_monoid M] [module R M]
  (b : basis ι R M) [nontrivial M] : 0 < fintype.card ι :=
fintype.card_pos_iff.mpr (basis.nonempty_index b)

-- TODO: make this `simp` when we have a typeclass like `module.finite_free R S`
lemma norm_zero_of_basis (b : basis ι R S) :
  norm R S 0 = 0 :=
by rw [← (algebra_map R S).map_zero, norm_algebra_map_of_basis b, zero_pow (basis.card_pos b)]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
lemma norm_algebra_map (x : K) : norm K (algebra_map K L x) = x ^ finrank K L :=
begin
  by_cases H : ∃ (s : finset L), nonempty (basis s K L),
  { rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero],
    rintros ⟨s, ⟨b⟩⟩,
    exact H ⟨s, ⟨b⟩⟩ },
end

section eq_prod_roots

lemma norm_gen_eq_prod_roots [algebra K S] (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  algebra_map K F (norm K pb.gen) =
    ((minpoly K pb.gen).map (algebra_map K F)).roots.prod :=
begin
  -- Write the LHS as the 0'th coefficient of `minpoly K pb.gen`
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_char_poly_coeff, char_poly_left_mul_matrix,
      ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_neg, ring_hom.map_one,
      ← polynomial.coeff_map, fintype.card_fin],
  -- Rewrite `minpoly K pb.gen` as a product over the roots.
  conv_lhs { rw polynomial.eq_prod_roots_of_splits hf },
  rw [polynomial.coeff_C_mul, polynomial.coeff_zero_multiset_prod, multiset.map_map,
      (minpoly.monic pb.is_integral_gen).leading_coeff, ring_hom.map_one, one_mul],
  -- Incorporate the `-1` from the `char_poly` back into the product.
  rw [← multiset.prod_repeat (-1 : F), ← pb.nat_degree_minpoly,
      polynomial.nat_degree_eq_card_roots hf, ← multiset.map_const, ← multiset.prod_map_mul],
  -- And conclude that both sides are the same.
  congr, convert multiset.map_id _, ext f, simp
end

end eq_prod_roots

end algebra

namespace ideal

/-- A nonzero ideal has the same rank (over a subring) as the whole ring. -/
lemma rank_eq {n m : Type*} [fintype n] [fintype m]
  (b : basis n R S) {I : ideal S} (hI : I ≠ ⊥) (c : basis m R I) :
  fintype.card m = fintype.card n :=
begin
  obtain ⟨a, ha⟩ := submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI),
  have : linear_independent R (λ i, b i • a),
  { have hb := b.linear_independent,
    rw fintype.linear_independent_iff at ⊢ hb,
    intros g hg,
    apply hb g,
    simp only [← smul_assoc, ← finset.sum_smul, smul_eq_zero] at hg,
    exact hg.resolve_right ha },
  exact le_antisymm
    (b.card_le_card_of_linear_independent (c.linear_independent.map' (submodule.subtype I)
      (linear_map.ker_eq_bot.mpr subtype.coe_injective)))
    (c.card_le_card_of_linear_independent this),
end

/-- If `I : ideal S` is not `⊥`, it has the same dimension over the PID `R` as `S` itself. -/
noncomputable def basis_of_ne_bot [is_principal_ideal_ring R] (b : basis ι R S)
  (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R I :=
let mc'' := submodule.basis_of_pid b (submodule.restrict_scalars R I),
    c' : basis (fin mc''.1) R I := mc''.2.map (submodule.restrict_scalars_equiv I) in
c'.reindex (fintype.equiv_of_card_eq (ideal.rank_eq b hI c'))

variables [normalization_monoid R]

/-- The ideal norm over `R` of an ideal `I : ideal S` is the determinant of an isomorphism `S ≃ₗ I`.

This is uniquely defined up to units in `R`, so we assume `normalization_monoid R`
to choose one of the non-units.

Note that such isomorphisms exist for all nonzero ideals if `S` is finite free over the PID `R`.
See `ideal.norm` for a version that chooses a value in this case.
-/
noncomputable def norm_aux (I : ideal S) (e : S ≃ₗ[R] I) : R :=
normalize $ linear_map.det (((submodule.subtype I).restrict_scalars R).comp e)

@[simp] lemma normalize_norm_aux (I : ideal S) (e : S ≃ₗ[R] I) :
  normalize (norm_aux I e) = norm_aux I e :=
normalize_idem _

/-
@[simp] lemma basis.reindex_refl {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  (b : basis ι R M) : b.reindex (equiv.refl _) = b :=
by { ext, simp }
-/

/-
lemma basis.associated_det_of_eq_linear_equiv_comp {R M : Type*} [integral_domain R]
  [add_comm_group M] [module R M] (b : basis ι R M) (v v' : ι → M) (f : M ≃ₗ[R] M)
  (h : ∀ i, v i = f (v' i)) : associated (b.det v) (b.det v') :=
begin
  suffices : associated (b.det (f.to_linear_map ∘ v')) (b.det v'),
  { convert this, ext i, simpa using h i },
  rw [← one_mul (b.det v'), b.det_comp],
  exact associated_mul_mul (associated_one_iff_is_unit.mpr f.is_unit_det') (associated.refl _)
end
-/

lemma linear_map.associated_det_of_eq_comp {R M : Type*} [integral_domain R]
  [add_comm_group M] [module R M] (e : M ≃ₗ[R] M) (f f' : M →ₗ[R] M)
  (h : ∀ x, f x = f' (e x)) : associated f.det f'.det :=
begin
  suffices : associated (f'.comp ↑e).det f'.det,
  { convert this using 2, ext x, simpa using h x },
  rw [← mul_one f'.det, linear_map.det_comp],
  exact associated_mul_mul (associated.refl _) (associated_one_iff_is_unit.mpr e.is_unit_det')
end

/-
lemma associated_det_map_basis_aux {R M N n : Type*} [integral_domain R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N] [fintype n]
  (b : basis n R M) (c c' : basis n R N) (f : N →ₗ[R] M) :
  associated (b.det (f ∘ c)) (b.det (f ∘ c')) :=
begin
  let g : M ≃ₗ[R] N := b.equiv c (equiv.refl _),
  have g_symm_comp_self : g.symm ∘ g = id, { ext, apply g.symm_apply_apply },
  have det_eq : ∀ (c : basis n R N),
    b.det (f ∘ c) = linear_map.det (g.to_linear_map.comp f) * (b.map g).det c,
  { intro c,
    rw [← function.left_id (f ∘ c), ← g_symm_comp_self, function.comp.assoc, ← basis.det_map,
        ← g.coe_to_linear_map, ← function.comp.assoc, ← linear_map.coe_comp, basis.det_comp] },
  rw [det_eq c, det_eq c'],
  refine associated_mul_mul (associated.refl _) _,
  refine basis.associated_det_of_eq_linear_equiv_comp _ _ _ (c'.equiv c (equiv.refl _)) (λ i, _),
  rw [← c'.map_apply, c'.map_equiv, c.reindex_apply, equiv.symm_symm, equiv.refl_apply]
end
-/

lemma associated_det_comp_equiv {R M N : Type*} [integral_domain R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (f : N →ₗ[R] M) (e e' : M ≃ₗ[R] N) :
  associated (f.comp ↑e).det (f.comp ↑e').det :=
begin
  refine linear_map.associated_det_of_eq_comp (e.trans e'.symm) _ _ _,
  intro x,
  simp only [linear_map.comp_apply, linear_equiv.coe_coe, linear_equiv.trans_apply,
             linear_equiv.apply_symm_apply],
end

@[simp] lemma submodule.coe_subtype {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  (S : submodule R M) :
  (S.subtype : S → M) = coe := rfl

@[simp] lemma normalize_associated_iff {x y : R} :
  associated (normalize x) y ↔ associated x y :=
⟨λ h, associated_normalize.trans h,
 λ h, normalize_associated.trans h⟩

/-- `norm_aux` does not depend on the choice of equiv `S ≃ₗ I`, up to units. -/
lemma norm_aux_associated (I : ideal S) (e e' : S ≃ₗ[R] I) :
  associated (norm_aux I e) (linear_map.det $ (I.subtype.restrict_scalars R).comp e') :=
by { simp only [norm_aux, normalize_associated_iff], apply associated_det_comp_equiv }

/-- `norm_aux` does not depend on the choice of equiv `S ≃ₗ I`, up to units. -/
lemma eq_norm_aux (I : ideal S) (e e' : S ≃ₗ[R] I) :
  normalize (linear_map.det $ (I.subtype.restrict_scalars R).comp e') = norm_aux I e :=
begin
  rw ← normalize_norm_aux,
  refine normalize_eq_normalize_iff.mpr (dvd_dvd_of_associated (associated.symm _)),
  apply norm_aux_associated
end

@[simp] lemma linear_map.coe_restrict_scalars (R : Type*) {S M M' : Type*}
  [semiring R] [semiring S] [add_comm_monoid M] [add_comm_monoid M']
  [module R M] [module R M'] [module S M] [module S M'] [compatible_smul M M' R S]
  (f : M →ₗ[S] M') :
  (f.restrict_scalars R : M → M') = f :=
rfl

@[simp] lemma coe_restrict_scalars (I : ideal S) :
  (I.restrict_scalars R : set S) = I :=
rfl

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp] lemma restrict_scalars_mul (I J : ideal S) :
  (I * J).restrict_scalars R = I.restrict_scalars R * J.restrict_scalars R :=
le_antisymm
  (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, submodule.mul_mem_mul hx hy)
    (submodule.zero_mem _)
    (λ x y, submodule.add_mem _)
    (λ c x hx, submodule.mul_induction_on hx
      (λ x hx y hy, by simpa only [smul_eq_mul, mul_assoc] using submodule.mul_mem_mul
        (show c • x ∈ I.restrict_scalars R, from ideal.mul_mem_left I c hx)
        hy)
      (by simp)
      (λ x y hx hy, by simpa only [smul_add] using submodule.add_mem _ hx hy)
      (λ c' x hx, by simpa only [smul_comm c c'] using submodule.smul_mem _ c' hx)))
  (submodule.mul_le.mpr (λ x hx y hy, ideal.mul_mem_mul hx hy))

/-
lemma norm_aux_mul (I J : ideal S)
  (eI : S ≃ₗ[R] I) (eJ : S ≃ₗ[R] J) (eIJ : S ≃ₗ[R] (I * J : ideal _)) :
  norm_aux (I * J) eIJ = norm_aux I eI * norm_aux J eJ :=
begin
  unfold norm_aux,
  rw [← normalize.map_mul, ← linear_map.det.map_mul, normalize_eq_normalize_iff],
  apply dvd_dvd_of_associated,
  refine linear_map.associated_det_of_eq_comp (linear_equiv.refl _ _) _ _ _,
  intro x,
  simp
end
-/

variables [is_principal_ideal_ring R]

open_locale classical

section

variables (R)

/-- The norm over `R` of an ideal `I` in `S` is the determinant of a basis for `I`.

This requires an `R`-basis on `S`; if there is no such basis the result is always `1`.

We define that the norm of `⊥` is 0.
-/
protected noncomputable def norm (I : ideal S) : R :=
if hI : I = ⊥ then 0
else if hS : ∃ (s : set S) (b : basis s R S), s.finite
     then norm_aux I (hS.some_spec.some.equiv
       (@ideal.basis_of_ne_bot _ _ _ _ _ _ hS.some_spec.some_spec.some _ hS.some_spec.some _ hI)
       (equiv.refl _))
     else 1

end

@[simp] lemma norm_bot : ideal.norm R (⊥ : ideal S) = 0 := dif_pos rfl

@[simp] lemma normalize_det_equiv {n : Type*} [fintype n]
  (b : basis n R S) (I : ideal S) (hI : I ≠ ⊥)
  (e : S ≃ₗ[R] I := b.equiv (I.basis_of_ne_bot b hI) (equiv.refl _)) :
  normalize ((I.subtype.restrict_scalars R).comp ↑e).det = I.norm R :=
begin
  unfold ideal.norm,
  rw dif_neg hI,
  have hS : ∃ (s : set S) (b : basis s R S), s.finite,
  { exact ⟨_, b.reindex_range, set.finite_range b⟩ },
  letI : fintype hS.some := hS.some_spec.some_spec.some,
  rw dif_pos hS,
  apply eq_norm_aux
end

open submodule

/-- A basis on `S` gives a basis on `ideal.span {x}`, by multiplying everything by `x`. -/
noncomputable def basis_span_singleton (b : basis ι R S) {x : S} (hx : x ≠ 0) :
  basis ι R (span ({x} : set S)) :=
b.map (linear_equiv.trans
  (linear_equiv.of_injective (algebra.lmul R S x) (ker_eq_bot.mpr (algebra.lmul_injective hx))) $
  linear_equiv.trans
    (linear_equiv.of_eq _ _ (by { ext, simp [mem_span_singleton', mul_comm] }))
    (restrict_scalars_equiv (span ({x} : set S))))

@[simp] lemma basis_span_singleton_apply (b : basis ι R S) {x : S} (hx : x ≠ 0) (i : ι) :
  basis_span_singleton b hx i = ⟨x * b i, mem_span_singleton.mpr (dvd_mul_right _ _)⟩ :=
begin
  ext,
  simp only [basis_span_singleton, basis.map_apply, linear_equiv.trans_apply, subtype.coe_mk,
      restrict_scalars_equiv_apply, linear_equiv.of_injective_apply, algebra.lmul_apply,
      linear_equiv.coe_of_eq_apply]
end

@[simp] lemma constr_basis_span_singleton
  {N : Type*} [semiring N] [module N S] [smul_comm_class R N S]
  (b : basis ι R S) {x : S} (hx : x ≠ 0) :
  b.constr N (coe ∘ basis_span_singleton b hx) = algebra.lmul R S x :=
b.ext (λ i, by rw [basis.constr_basis, function.comp_app, basis_span_singleton_apply,
                   subtype.coe_mk, algebra.lmul_apply])

@[simp] lemma ideal.span_zero_singleton : span ({0} : set S) = ⊥ :=
submodule.span_zero_singleton

-- TODO: make this `simp` when we have a typeclass like `module.finite_free R S`
/-- The ideal norm agrees with the algebra norm on ideals generated by one element. -/
lemma norm_span_singleton (b : basis ι R S) (x : S) :
  ideal.norm R (span ({x} : set S)) = normalize (algebra.norm R S x) :=
begin
  by_cases hx : x = 0,
  { simp [hx, algebra.norm_zero_of_basis b] },
  have : span {x} ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp hx,
  rw [algebra.norm_apply,
      ← normalize_det_equiv b (span {x}) this (b.equiv (basis_span_singleton b hx) (equiv.refl _))],
  congr,
  refine b.ext (λ i, _),
  simp
end

@[simp] lemma span_singleton_one' : span ({1} : set S) = ⊤ :=
span_singleton_one

@[simp] lemma norm_top : ideal.norm R (⊤ : ideal S) = 1 :=
begin
  by_cases hS : ∃ (s : set S) (b : basis s R S), s.finite,
  swap, { exact (dif_neg top_ne_bot).trans (dif_neg hS) },
  letI : fintype hS.some := hS.some_spec.some_spec.some,
  rw [← span_singleton_one', norm_span_singleton hS.some_spec.some, monoid_hom.map_one,
      normalize.map_one]
end

/-- Multiplicity of the norm -/
theorem norm_mul (I J : ideal S) : (I * J).norm R = I.norm R * J.norm R :=
begin
  by_cases hI : I = ⊥,
  { simp [hI] },
  by_cases hJ : J = ⊥,
  { simp [hJ] },
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or hI hJ),
  unfold ideal.norm,
  rw [dif_neg hI, dif_neg hJ, dif_neg hIJ],
  split_ifs with hS,
  swap, { simp }, -- Handle the non-free-finite case first.
  letI : fintype hS.some := hS.some_spec.some_spec.some,
  sorry
end

lemma algebra_map_norm_mem (b : basis ι R S) (I : ideal S) :
  algebra_map R S (I.norm R) ∈ I :=
sorry -- TODO: via Lagrange's theorem?

lemma is_unit_norm_iff (b : basis ι R S) (x : S) :
  is_unit (ideal.norm R (span ({x} : set S))) ↔ is_unit x :=
iff.trans
  ⟨λ h, ideal.eq_top_of_is_unit_mem _ (algebra_map_norm_mem b _) ((algebra_map R S).is_unit_map h),
   λ h, have is_unit (1 : R) := is_unit_one, by rwa [h, ideal.norm_top]⟩
  span_singleton_eq_top

end ideal

@[simp] lemma is_unit_normalize [normalization_monoid S] {x : S} :
  is_unit (normalize x) ↔ is_unit x :=
by rw [← @normalize_eq_one _ _ _ _ x, ← normalize_eq_one, normalize_idem]

theorem algebra.is_unit_norm_iff [is_principal_ideal_ring R] [normalization_monoid R]
  (b : basis ι R S) (x : S) :
  is_unit (algebra.norm R S x) ↔ is_unit x :=
by rw [← is_unit_normalize, ← ideal.norm_span_singleton b x, ideal.is_unit_norm_iff b]

section int

/-! ### The ideal norm as an integer

When the base ring is `ℤ`, we can show multiplicity by applying the Chinese Remainder Theorem.
-/

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix. -/
theorem submodule.smith_normal_form {O : Type*} [add_comm_group O] [module R O]
  {ι : Type*} [fintype ι] (b : basis ι R O) (N : submodule R O) :
  ∃ (n : ℕ) (b' : basis ι R O) (f : fin n → ι) (a : fin n → R) (ab' : basis (fin n) R N),
  ∀ i, (ab' i : O) = a i • b' (f i) :=
sorry -- TODO: strengthen `submodule.basis_of_pid`

/-- If `S` is a finite free extension of a PID `R`, then any nonzero ideal `I` is free
and we can find a basis for `S` and `I` such that the inclusion map is a diagonal matrix. -/
theorem ideal.smith_normal_form (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ∃ (b' : basis ι R S) (a : ι → R) (ab' : basis ι R I),
  ∀ i, (ab' i : S) = a i • b' i :=
begin
  obtain ⟨n, b', g', a', ab', ab_eq⟩ := submodule.smith_normal_form b (I.restrict_scalars R),
  let ab : basis (fin n) R I := ab'.map I.restrict_scalars_equiv,
  have g'_inj := sorry, -- because `ab'` is linear independent
  have g'_bij := (fintype.bijective_iff_injective_and_card g').mpr ⟨g'_inj, ideal.rank_eq b' hI ab⟩,
  let g : fin n ≃ ι := equiv.of_bijective g' g'_bij,
  have g_apply : ∀ i, g i = g' i := λ i, rfl,
  let a : ι → R := a' ∘ g.symm,
  have a_apply : ∀ i, a i = a' (g.symm i) := λ i, rfl,
  use [b', a, ab.reindex g],
  intro i,
  rw [← g.apply_symm_apply i, a_apply, g.symm_apply_apply, basis.reindex_apply, g.symm_apply_apply],
  simp only [ab_eq, ab'.map_apply, I.restrict_scalars_equiv_apply, equiv.of_bijective_apply],
end

noncomputable def ideal.ring_basis (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R S := (ideal.smith_normal_form b I hI).some

noncomputable def ideal.self_basis (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R I := (ideal.smith_normal_form b I hI).some_spec.some_spec.some

noncomputable def ideal.smith_coeffs (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ι → R := (ideal.smith_normal_form b I hI).some_spec.some

@[simp]
lemma ideal.self_basis_def (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ∀ i, (ideal.self_basis b I hI i : S) = ideal.smith_coeffs b I hI i • ideal.ring_basis b I hI i :=
(ideal.smith_normal_form b I hI).some_spec.some_spec.some_spec

-- TODO: why doesn't this work "normally"?
lemma normalize_prod {ι : Type*} (a : ι → ℤ) (s : finset ι) :
  normalize (∏ i in s, a i) = ∏ i in s, normalize (a i) :=
monoid_hom.map_prod (normalize.to_monoid_hom : ℤ →* ℤ) a s

/-
/-- If `P` is a submodule of `M`, and `f : M →ₗ N` has a kernel that contains `P`,
lift it to the quotient by `P`. -/
def submodule.quotient.lift {M N : Type*}
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (f : M →ₗ[R] N) (hf : ∀ x ∈ P, f x = 0) :
  P.quotient →ₗ[R] N :=
{ to_fun := λ x, quotient.lift_on' x f $ λ a b h, eq_of_sub_eq_zero $ by rw [← f.map_sub, hf _ h],
  map_add' := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ f.map_add,
  map_smul' := λ c a, quotient.induction_on' a (f.map_smul c) }

@[simp] def submodule.quotient.lift_mk {M N : Type*}
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (f : M →ₗ[R] N) (hf : ∀ x ∈ P, f x = 0) (x : M) :
  submodule.quotient.lift P f hf (submodule.quotient.mk x) = f x :=
rfl

def submodule.quotient.mk_hom {M : Type*} [add_comm_group M] [module R M]
  {P : submodule R M} : M →ₗ[R] P.quotient :=
{ to_fun := submodule.quotient.mk,
  map_add' := λ x y, submodule.quotient.mk_add _,
  map_smul' := λ c x, submodule.quotient.mk_smul _ }

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`, and `f : M →ₗ N` maps `P` to a
subset of `Q`, then lift `f` to a map `P.quotient →ₗ Q.quotient`. -/
def submodule.quotient.map {M N : Type*}
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N) (f : M →ₗ[R] N) (hf : ∀ x ∈ P, f x ∈ Q) :
  P.quotient →ₗ[R] Q.quotient :=
submodule.quotient.lift P (submodule.quotient.mk_hom.comp f)
  (λ x hx, (submodule.quotient.mk_eq_zero _).mpr (hf _ hx))

@[simp] def submodule.quotient.map_mk {M N : Type*}
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N) (f : M →ₗ[R] N) (hf : ∀ x ∈ P, f x ∈ Q)
  (x : M) : submodule.quotient.map P Q f hf (submodule.quotient.mk x) = submodule.quotient.mk (f x) :=
rfl
-/

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M.quotient` is equivalent to `N.quotient`. -/
@[simps] def submodule.quotient.equiv {M N : Type*}
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N)
  (f : M ≃ₗ[R] N) (hf : P.map ↑f = Q) : P.quotient ≃ₗ[R] Q.quotient :=
{ to_fun := P.mapq Q ↑f (λ x hx, hf ▸ submodule.mem_map_of_mem hx),
  inv_fun := Q.mapq P ↑f.symm (λ x hx, begin
    rw [← hf, submodule.mem_map] at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    simpa
  end),
  left_inv := λ x, quotient.induction_on' x (by simp),
  right_inv := λ x, quotient.induction_on' x (by simp),
  .. P.mapq Q ↑f (λ x hx, hf ▸ submodule.mem_map_of_mem hx) }

.

-- TODO: make this the main `submodule.quotient.module` instance
instance submodule.quotient.module'
  {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  (P : submodule S M) : module R P.quotient :=
module.of_core { smul := λ c x, algebra_map R S c • x,
                 smul_add := λ c x y, smul_add _ _ _,
                 add_smul := λ c c' x, by simp only [ring_hom.map_add, add_smul],
                 mul_smul := λ c c' x, by simp only [ring_hom.map_mul, mul_action.mul_smul],
                 one_smul := λ x, by simp only [ring_hom.map_one, one_smul] }

@[simp] lemma smul_mk {M : Type*} [add_comm_group M] [module R M] [module S M]
  [is_scalar_tower R S M] (P : submodule S M) (c : R) (x : M) :
  (c • submodule.quotient.mk x : P.quotient) = submodule.quotient.mk (c • x) :=
show submodule.quotient.mk (algebra_map R S c • x) = submodule.quotient.mk (c • x),
by rw algebra_map_smul

instance {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  (P : submodule S M) : is_scalar_tower R S P.quotient :=
{ smul_assoc := λ x y z, show (x • y) • z = algebra_map R S x • y • z,
                         by rw [← smul_assoc, algebra_map_smul] }

/-- Restricting the scalars of a submodule doesn't change the quotient you get. -/
@[simps] def submodule.restrict_scalars_quotient_equiv {M : Type*}
  [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  (P : submodule S M) : (P.restrict_scalars R).quotient ≃ₗ[R] P.quotient :=
{ to_fun := quot.map id (λ x y, id),
  inv_fun := quot.map id (λ x y, id),
  left_inv := λ x, quot.induction_on x (λ x', rfl),
  right_inv := λ x, quot.induction_on x (λ x', rfl),
  map_add' := λ x y, quot.induction_on₂ x y (λ x' y', rfl),
  map_smul' := λ c x, quot.induction_on x (λ x',
    by { rw [submodule.quotient.quot_mk_eq_mk, smul_mk, ← algebra_map_smul S c x'],
         exact submodule.quotient.mk_smul _ }) }

@[simps] def submodule_span_quotient_equiv (s : set S) :
  (submodule.span S s).quotient ≃ₗ[S] (ideal.span s).quotient :=
{ to_fun := quot.map id (λ x y, id),
  inv_fun := quot.map id (λ x y, id),
  left_inv := λ x, quot.induction_on x (λ x', rfl),
  right_inv := λ x, quot.induction_on x (λ x', rfl),
  map_add' := λ x y, quot.induction_on₂ x y (λ x' y', rfl),
  map_smul' := λ c x, quot.induction_on x (λ x', rfl) }

lemma basis.mem_submodule_iff {M : Type*} [add_comm_group M] [module R M] {P : submodule R M}
  (b : basis ι R P) {x : M} :
  x ∈ P ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
begin
  split,
  { intro hx, use b.equiv_fun ⟨x, hx⟩,
    show P.subtype ⟨x, hx⟩ = ∑ (i : ι), b.equiv_fun ⟨x, hx⟩ i • P.subtype (b i),
    convert congr_arg P.subtype (b.sum_equiv_fun ⟨x, hx⟩).symm,
    simp only [linear_map.map_sum, linear_map.map_smul] },
  { rintros ⟨c, rfl⟩,
    exact P.sum_mem (λ i _, P.smul_mem _ (b i).2) },
end

lemma basis.mem_ideal_iff {I : ideal S} (b : basis ι R I) {x : S} :
  x ∈ I ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
(b.map I.restrict_scalars_equiv.symm).mem_submodule_iff

@[simp] lemma basis.repr_sum_self {M : Type*}
  [add_comm_monoid M] [module R M] (b : basis ι R M) (c : ι → R) :
  ⇑(b.repr (∑ i, c i • b i)) = c :=
begin
  ext j,
  simp only [linear_equiv.map_sum, linear_equiv.map_smul, basis.repr_self, finsupp.smul_single,
             smul_eq_mul, mul_one, finset.sum_apply'],
  rw [finset.sum_eq_single j, finsupp.single_eq_same],
  { rintros i - hi, exact finsupp.single_eq_of_ne hi },
  { intros, have := finset.mem_univ j, contradiction }
end

lemma le_comap_single_pi {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  (p : ∀ i, submodule R (M i)) {i} :
  p i ≤ submodule.comap (single i) (submodule.pi set.univ p) :=
begin
  intros x hx,
  rw [submodule.mem_comap, submodule.mem_pi],
  rintros j -,
  by_cases h : j = i,
  { rwa [h, coe_single, pi.single_eq_same] },
  { rw [coe_single, pi.single_eq_of_ne h], exact (p j).zero_mem }
end

/-- Lift a family of maps to the direct sum of quotients. -/
def submodule.pi_quotient_lift {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) :
  (Π i, (p i).quotient) →ₗ[R] q.quotient :=
linear_map.lsum R (λ i, (p i).quotient) R (λ i, (p i).mapq q (f i) (hf i))

@[simp] lemma submodule.pi_quotient_lift_mk {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (x : Π i, M i) :
  submodule.pi_quotient_lift p q f hf (λ i, submodule.quotient.mk (x i)) =
    submodule.quotient.mk (linear_map.lsum _ _ R f x) :=
by rw [submodule.pi_quotient_lift, linear_map.lsum_apply, linear_map.sum_apply,
       ← submodule.mkq_apply, linear_map.lsum_apply, linear_map.sum_apply, linear_map.map_sum];
   simp only [linear_map.coe_proj, submodule.mapq_apply, submodule.mkq_apply, linear_map.comp_apply]

@[simp] lemma submodule.pi_quotient_lift_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (i) (x : (p i).quotient) :
  submodule.pi_quotient_lift p q f hf (pi.single i x) =
    submodule.mapq _ _ (f i) (hf i) x :=
begin
  simp_rw [submodule.pi_quotient_lift, linear_map.lsum_apply, linear_map.sum_apply,
           linear_map.comp_apply, linear_map.proj_apply],
  rw finset.sum_eq_single i,
  { rw pi.single_eq_same },
  { rintros j - hj, rw [pi.single_eq_of_ne hj, linear_map.map_zero] },
  { intros, have := finset.mem_univ i, contradiction },
end

/-- Lift a family of maps to a quotient of direct sums. -/
def submodule.quotient_pi_lift {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : ι → Type*} [∀ i, add_comm_group (N i)] [∀ i, module R (N i)]
  (p : ∀ i, submodule R (M i))
  (f : Π i, M i →ₗ[R] N i) (hf : ∀ i, p i ≤ ker (f i)) :
  (submodule.pi set.univ p).quotient →ₗ[R] Π i, N i :=
(submodule.pi set.univ p).liftq (linear_map.pi (λ i, (f i).comp (linear_map.proj i)))
  (λ x hx, mem_ker.mpr (by { ext i, simpa using hf i (submodule.mem_pi.mp hx i (set.mem_univ i)) }))

@[simp] lemma submodule.quotient_pi_lift_mk {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : ι → Type*} [∀ i, add_comm_group (N i)] [∀ i, module R (N i)]
  (p : ∀ i, submodule R (M i))
  (f : Π i, M i →ₗ[R] N i) (hf : ∀ i, p i ≤ ker (f i)) (x : Π i, M i) :
  submodule.quotient_pi_lift p f hf (submodule.quotient.mk x) = λ i, f i (x i) :=
rfl

@[simp] lemma sum_pi_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_monoid (M i)] (x : Π i, M i) :
  ∑ i, pi.single i (x i) = x :=
funext (λ j, begin
  rw [finset.sum_apply, finset.sum_eq_single j],
  { simp },
  { rintros i - hi, exact pi.single_eq_of_ne hi.symm _ },
  { simp }
end)

@[simp] lemma linear_map.lsum_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)] :
  linear_map.lsum R M R linear_map.single = linear_map.id :=
linear_map.ext (λ x, by simp)

/-- The quotient of a direct sum is the direct sum of quotients -/
@[simps] def submodule.quotient_pi {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  (p : ∀ i, submodule R (M i)) :
  (submodule.pi set.univ p).quotient ≃ₗ[R] Π i, (p i).quotient :=
{ to_fun := submodule.quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simpa using le_refl (p i)),
  inv_fun := submodule.pi_quotient_lift p (submodule.pi set.univ p)
    linear_map.single (λ i, le_comap_single_pi p),
  left_inv := λ x, quotient.induction_on' x (λ x',
    by simp_rw [submodule.quotient.mk'_eq_mk, submodule.quotient_pi_lift_mk, submodule.mkq_apply,
                submodule.pi_quotient_lift_mk, linear_map.lsum_single, linear_map.id_apply]),
  right_inv := begin
    rw [function.right_inverse_iff_comp, ← linear_map.coe_comp, ← @linear_map.id_coe R],
    refine congr_arg _ (linear_map.pi_ext (λ i x, quotient.induction_on' x (λ x', funext $ λ j, _))),
    rw [linear_map.comp_apply, submodule.pi_quotient_lift_single, submodule.quotient.mk'_eq_mk,
        submodule.mapq_apply, submodule.quotient_pi_lift_mk, linear_map.id_apply],
    sorry -- Why doesn't Lean see that this is the same?!
  end,
  .. submodule.quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simpa using le_refl (p i)) }

.

variables {M : Type*} [add_comm_group M] [module R M]

namespace submodule

section

open_locale classical

/-- The norm of a submodule `S`, defined as the cardinality of `S.quotient`,
if `S.quotient` is finite, and `0` otherwise. -/
noncomputable def card_norm (S : submodule R M) : ℕ :=
if h : nonempty (fintype S.quotient) then @fintype.card S.quotient h.some else 0

@[simp] lemma card_norm_apply (S : submodule R M) [h : fintype S.quotient] :
  card_norm S = fintype.card S.quotient :=
by convert dif_pos (nonempty.intro h) -- `convert` deals with the different `fintype` instances

instance [infinite M] : infinite (⊥ : submodule R M).quotient :=
infinite.of_injective submodule.quotient.mk $ λ x y h, sub_eq_zero.mp $ (quotient.eq ⊥).mp h

@[simp] lemma card_norm_bot [infinite M] : card_norm (⊥ : submodule R M) = 0 :=
dif_neg (by simp; apply_instance)

instance : unique (⊤ : submodule R M).quotient :=
{ default := 0,
  uniq := λ x, quotient.induction_on' x $ λ x, (quotient.eq ⊤).mpr mem_top }

variables (R)

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps] def _root_.linear_equiv.of_subsingleton {N : Type*} [add_comm_monoid N] [module R N]
  [subsingleton M] [subsingleton N] : M ≃ₗ[R] N :=
{ to_fun := λ _, 0,
  inv_fun := λ _, 0,
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _,
  .. (0 : M →ₗ[R] N)}

variables {R}

instance quotient_top.fintype : fintype (⊤ : submodule R M).quotient :=
fintype.of_equiv punit $ equiv_of_subsingleton_of_subsingleton 0 0

@[simp] lemma card_norm_top : card_norm (⊤ : submodule R M) = 1 :=
calc card_norm ⊤ = fintype.card (submodule.quotient ⊤) : card_norm_apply _
... = fintype.card punit : fintype.card_eq.mpr ⟨equiv_of_subsingleton_of_subsingleton 0 0⟩
... = 1 : fintype.card_punit

end

end submodule

open submodule

/-- The quotient by the ideal generated by `a` is exactly `zmod a`. -/
def quotient_equiv (a : ℤ) : ideal.quotient (ideal.span ({a} : set ℤ)) ≃+* zmod a.nat_abs :=
sorry

/-- We can write the quotient of an ideal over a PID as a product of quotients by principal ideals. -/
noncomputable def ideal.quotient_equiv_pi_span [decidable_eq ι]
  (I : ideal S) (b : basis ι R S) (hI : I ≠ ⊥) :
  I.quotient ≃ₗ[R] Π i, (ideal.span ({I.smith_coeffs b hI i} : set R)).quotient :=
begin
  -- Choose `e : S ≃ₗ I` and a basis `b'` for `S` that turns the map
  -- `f := ((submodule.subtype I).restrict_scalars R).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e : S ≃ₗ[R] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[R] S := (I.subtype.restrict_scalars R).comp e,
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff, ab_eq],
    have : ∀ (c : ι → R) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → R)`,
  -- which maps `I` to `I' := Π i, a i ℤ`.
  let I' : submodule R (ι → R) := submodule.pi set.univ (λ i, ideal.span ({a i} : set R)),
  have : submodule.map ↑b'.equiv_fun (I.restrict_scalars R) = I',
  { ext x,
    simp only [submodule.mem_map, submodule.mem_pi, ideal.mem_span_singleton, set.mem_univ,
               submodule.restrict_scalars_mem, mem_I_iff, smul_eq_mul, forall_true_left,
               linear_equiv.coe_coe, basis.equiv_fun_apply],
    split,
    { rintros ⟨y, hy, rfl⟩ i, exact hy i },
    { rintros hdvd,
      refine ⟨∑ i, x i • b' i, λ i, _, _⟩; rwa b'.repr_sum_self,
      { exact hdvd i } } },
  exact I.restrict_scalars_quotient_equiv.symm.trans
    ((submodule.quotient.equiv (I.restrict_scalars R) I' b'.equiv_fun this).trans
    (submodule.quotient_pi _))
end

-- TODO: do we want to strengthen the equiv (e.g. ring equiv?)
/-- Ideal quotients over a free finite extension of `ℤ` are isomorphic to a direct product of `zmod`. -/
noncomputable def ideal.quotient_equiv_pi_zmod [decidable_eq ι]
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  I.quotient ≃ Π i, (zmod (I.smith_coeffs b hI i).nat_abs) :=
begin
  let a := I.smith_coeffs b hI,
  let e := I.quotient_equiv_pi_span b hI,
  let e' : (Π (i : ι), (ideal.span ({a i} : set ℤ)).quotient) ≃ Π (i : ι), zmod (a i).nat_abs :=
    equiv.Pi_congr (equiv.refl _) (λ i, (quotient_equiv (a i)).to_equiv),
  refine (_ : I.quotient ≃ₗ[ℤ] _).to_equiv.trans e',
  -- TODO: probably from the `module _ I.quotient` instance assuming `is_scalar_tower`
  haveI : unique (module ℤ I.quotient) := add_comm_group.int_module.unique,
  convert e
end

/-- A nonzero ideal over a free finite extension of `ℤ` has a finite quotient. -/
noncomputable def ideal.fintype_quotient_of_free_of_ne_bot [decidable_eq ι]
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  fintype I.quotient :=
begin
  let a := I.smith_coeffs b hI,
  let e := I.quotient_equiv_pi_zmod b hI,
  haveI : ∀ i, fact (0 < (a i).nat_abs) := sorry,
  exact fintype.of_equiv (Π i, zmod (a i).nat_abs) e.symm,
end

.

#print ideal.quotient

variables [infinite S] -- TODO: should be provable from [integral_domain S] and `basis ι ℤ S`

-- TODO: can we generalize this to other PIDs than ℤ?
theorem ideal.card_norm_eq_norm (b : basis ι ℤ S) (I : ideal S) :
  ideal.norm ℤ I = card_norm I :=
begin
  -- If `I` is the zero ideal, both sides are defined to equal 0.
  by_cases hI : I = ⊥,
  { rw [hI, ideal.norm_bot, card_norm_bot, int.coe_nat_zero] },

  -- Otherwise, `I.quotient` is isomorphic to a product of `zmod`s, so it is a fintype.
  letI := classical.dec_eq ι,
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e : S ≃ₗ[ℤ] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[ℤ] S := (I.subtype.restrict_scalars ℤ).comp e,
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff, ab_eq],
    have : ∀ (c : ι → ℤ) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },
  letI : fintype (quotient I) := ideal.fintype_quotient_of_free_of_ne_bot I b hI,

  -- Note that `ideal.norm ℤ I = det f` is equal to `∏ i, a i`,
  letI := classical.dec_eq ι,
  calc ideal.norm ℤ I
      = normalize (linear_map.det f) : (I.normalize_det_equiv b' hI e).symm
  ... = normalize (linear_map.to_matrix b' b' f).det : by rw det_to_matrix
  ... = normalize (matrix.diagonal a).det : _
  ... = normalize (∏ i, a i) : by rw det_diagonal
  ... = ∏ i, normalize (a i) : normalize_prod a finset.univ
  ... = fintype.card I.quotient : _
  ... = card_norm I : by rw card_norm_apply I,
  -- since `linear_map.to_matrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  { congr, ext i j,
    rw [to_matrix_apply, ha, linear_equiv.map_smul, basis.repr_self, finsupp.smul_single,
        smul_eq_mul, mul_one],
    by_cases h : i = j,
    { rw [h, diagonal_apply_eq, finsupp.single_eq_same] },
    { rw [diagonal_apply_ne h, finsupp.single_eq_of_ne (ne.symm h)] } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → ℤ)`,
  -- which maps `I.quotient` to `Π i, zmod (a i).nat_abs`.
  haveI : ∀ i, fact (0 < (a i).nat_abs) := sorry,
  simp_rw [fintype.card_eq.mpr ⟨ideal.quotient_equiv_pi_zmod I b hI⟩, fintype.card_pi, zmod.card],
  sorry -- TODO: `normalize = (↑) ∘ nat_abs`
end

.

/-- Chinese remainder theorem, specialized to two ideals. -/
def ideal.quotient_mul_equiv_quotient_prod (I J : ideal S) (coprime : I ⊔ J = ⊤) :
  (I * J).quotient ≃+* I.quotient × J.quotient :=
let f : fin 2 → ideal S := ![I, J] in
have hf : ∀ (i j : fin 2), i ≠ j → f i ⊔ f j = ⊤,
{ intros i j h, fin_cases i; fin_cases j; sorry },
sorry

/-- Multiplicity of the ideal norm, for coprime ideals.

This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
lemma card_norm_mul_of_coprime (b : basis ι ℤ S) (I J : ideal S) (coprime : I ⊔ J = ⊤) :
  card_norm (I * J) = card_norm I * card_norm J :=
begin
  by_cases hI : I = ⊥,
  { rw [hI, submodule.bot_mul, card_norm_bot, zero_mul] },
  by_cases hJ : J = ⊥,
  { rw [hJ, submodule.mul_bot, card_norm_bot, mul_zero] },
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or hI hJ),

  letI := classical.dec_eq ι,
  letI := I.fintype_quotient_of_free_of_ne_bot b hI,
  letI := J.fintype_quotient_of_free_of_ne_bot b hJ,
  letI := (I * J).fintype_quotient_of_free_of_ne_bot b hIJ,

  rw [card_norm_apply, card_norm_apply, card_norm_apply,
      fintype.card_eq.mpr ⟨(ideal.quotient_mul_equiv_quotient_prod I J coprime).to_equiv⟩,
      fintype.card_prod]
end

instance : comm_cancel_monoid_with_zero (ideal S) :=
{ .. (infer_instance : comm_monoid_with_zero (ideal S)) }

lemma ideal.is_unit_iff {I : ideal S} : is_unit I ↔ I = ⊤ := sorry

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
lemma card_norm_pow_of_prime (b : basis ι ℤ S) [unique_factorization_monoid (ideal S)]
  (P : ideal S) [P_prime : P.is_prime] {i : ℕ} :
  card_norm (P ^ i) = card_norm P ^ i :=
begin
  induction i with i ih,
  { simp },
  { rw [pow_succ (card_norm P), ← ih] }
end

/-- Multiplicity of the ideal norm in number rings. -/
theorem card_norm_mul (b : basis ι ℤ S) [unique_factorization_monoid (ideal S)] (I J : ideal S) :
  card_norm (I * J) = card_norm I * card_norm J :=
unique_factorization_monoid.induction_on_prime I (by simp)
  (λ I hI, by simp [ideal.is_unit_iff.mp hI, ideal.top_mul])
  (λ I P (hI : I ≠ ⊥) hP ih, _)

end int
