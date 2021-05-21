/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.char_poly.coeff
import linear_algebra.determinant
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

open_locale classical

section

variables (R)

def restrict_scalars_equiv (I : ideal S) : submodule.restrict_scalars R I ≃ₗ[R] I :=
-- Everything is defeq except scalar multiplication.
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  map_smul' := λ c x,
    by { ext,
         cases x with x hx,
         rw [← is_scalar_tower.algebra_map_smul S c (⟨x, hx⟩ : I),
             submodule.coe_smul, submodule.coe_smul, is_scalar_tower.algebra_map_smul] },
  .. add_equiv.refl I }

@[simp] lemma coe_restrict_scalars_equiv (I : ideal S) (x : submodule.restrict_scalars R I) :
  (restrict_scalars_equiv R I x : S) = x :=
rfl

@[simp] lemma coe_restrict_scalars_equiv_symm (I : ideal S) (x : I) :
  ((restrict_scalars_equiv R I).symm x : S) = x :=
rfl

/-- `I.subtype R` is the `R`-linear embedding of `I : ideal S` into `S`. -/
@[simps]
def subtype (I : ideal S) : I →ₗ[R] S :=
{ to_fun := λ x, x,
  map_smul' := λ c x, by rw [← is_scalar_tower.algebra_map_smul S c x, submodule.coe_smul,
                             is_scalar_tower.algebra_map_smul],
  .. submodule.subtype I }

end

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
    c' : basis (fin mc''.1) R I := mc''.2.map (restrict_scalars_equiv R I) in
c'.reindex (fintype.equiv_of_card_eq (ideal.rank_eq b hI c'))

variables [normalization_monoid R]

/-- The ideal norm over `R` of an ideal `I : ideal S` is the determinant of an isomorphism `S ≃ₗ I`.

This is uniquely defined up to units in `R`, so we assume `normalization_monoid R`
to choose one of the non-units.

Note that such isomorphisms exist for all nonzero ideals if `S` is finite free over the PID `R`.
See `ideal.norm` for a version that chooses a value in this case.
-/
noncomputable def norm_aux (I : ideal S) (e : S ≃ₗ[R] I) : R :=
normalize $ linear_map.det ((ideal.subtype R I).comp e)

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
  associated (norm_aux I e) (linear_map.det $ (ideal.subtype R I).comp e') :=
by { simp only [norm_aux, normalize_associated_iff], apply associated_det_comp_equiv }

/-- `norm_aux` does not depend on the choice of equiv `S ≃ₗ I`, up to units. -/
lemma eq_norm_aux (I : ideal S) (e e' : S ≃ₗ[R] I) :
  normalize (linear_map.det $ (ideal.subtype R I).comp e') = norm_aux I e :=
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

lemma norm_aux_mul (I J : ideal S)
  (eI : S ≃ₗ[R] I) (eJ : S ≃ₗ[R] J) (eIJ : S ≃ₗ[R] (I * J : ideal _)) :
  norm_aux (I * J) eIJ = norm_aux I eI * norm_aux J eJ :=
begin
  unfold norm_aux,
  rw [← normalize.map_mul, ← linear_map.det.map_mul, normalize_eq_normalize_iff],
  apply dvd_dvd_of_associated,
  refine linear_map.associated_det_of_eq_comp _ _ _ _;
    sorry
end

variables [is_principal_ideal_ring R]

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
  normalize ((I.subtype R).comp ↑e).det = I.norm R :=
begin
  unfold ideal.norm,
  rw dif_neg hI,
  have hS : ∃ (s : set S) (b : basis s R S), s.finite,
  { exact ⟨_, b.reindex_range, set.finite_range b⟩ },
  letI : fintype hS.some := hS.some_spec.some_spec.some,
  rw dif_pos hS,
  apply eq_norm_aux
end

/-- A basis on `S` gives a basis on `ideal.span {x}`, by multiplying everything by `x`. -/
noncomputable def basis_span_singleton (b : basis ι R S) {x : S} (hx : x ≠ 0) :
  basis ι R (span ({x} : set S)) :=
b.map (linear_equiv.trans
  (linear_equiv.of_injective (algebra.lmul R S x) (ker_eq_bot.mpr (algebra.lmul_injective hx))) $
  linear_equiv.trans
    (linear_equiv.of_eq _ _ (by { ext, simp [mem_span_singleton', mul_comm] }))
    (restrict_scalars_equiv R (span ({x} : set S))))

@[simp] lemma basis_span_singleton_apply (b : basis ι R S) {x : S} (hx : x ≠ 0) (i : ι) :
  basis_span_singleton b hx i = ⟨x * b i, mem_span_singleton.mpr (dvd_mul_right _ _)⟩ :=
begin
  ext,
  simp only [basis_span_singleton, basis.map_apply, linear_equiv.trans_apply, subtype.coe_mk,
      coe_restrict_scalars_equiv, linear_equiv.of_injective_apply, algebra.lmul_apply,
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
  exact norm_aux_mul hS.some_spec.some I J hI hJ hIJ
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
