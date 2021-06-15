/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import linear_algebra.basis
import linear_algebra.finsupp_vector_space
import ring_theory.principal_ideal_domain
import ring_theory.finiteness

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[integral_domain R] [is_principal_ideal_ring R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

 - `submodule.induction_on_rank`: if `P` holds for `⊥ : submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
   on all submodules

 - `submodule.exists_basis_of_pid`: if `R` is a PID, then `N : submodule R M` is
   free and finitely generated. This is the first part of the structure theorem
   for modules.

- `submodule.exists_smith_normal_form`: if `R` is a PID, then `M` has a basis
  `bN` and `N` has a basis `abN` such that `abN i = a i • bN i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/

open_locale big_operators

section comm_ring

universes u v

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables {ι : Type*} (b : basis ι R M)

open submodule.is_principal

lemma eq_bot_of_rank_eq_zero [no_zero_divisors R] (b : basis ι R M) (N : submodule R M)
  (rank_eq : ∀ {m : ℕ} (v : fin m → N),
    linear_independent R (coe ∘ v : fin m → M) → m = 0) :
  N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  contrapose! rank_eq with x_ne,
  refine ⟨1, λ _, ⟨x, hx⟩, _, one_ne_zero⟩,
  rw fintype.linear_independent_iff,
  rintros g sum_eq i,
  fin_cases i,
  simp only [function.const_apply, fin.default_eq_zero, submodule.coe_mk, univ_unique,
             function.comp_const, finset.sum_singleton] at sum_eq,
  exact (b.smul_eq_zero.mp sum_eq).resolve_right x_ne
end

open submodule

lemma eq_bot_of_generator_maximal_map_eq_zero (b : basis ι R M) {N : submodule R M}
  {ϕ : M →ₗ[R] R} (hϕ : ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ)
  [(N.map ϕ).is_principal] (hgen : generator (N.map ϕ) = 0) : N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  refine b.ext_elem (λ i, _),
  rw (eq_bot_iff_generator_eq_zero _).mpr hgen at hϕ,
  rw [linear_equiv.map_zero, finsupp.zero_apply],
  exact (submodule.eq_bot_iff _).mp (hϕ ((finsupp.lapply i).comp b.repr) bot_le) _ ⟨x, hx, rfl⟩
end

lemma eq_bot_of_generator_maximal_range_eq_zero {N O : submodule R M} (b : basis ι R O)
  (hNO : N ≤ O)
  {ϕ : O →ₗ[R] R} (hϕ : ∀ (ψ : O →ₗ[R] R), (ϕ.comp $ of_le hNO).range ≤ (ψ.comp $ of_le hNO).range →
    (ψ.comp $ of_le hNO).range = (ϕ.comp (of_le hNO)).range)
  [(ϕ.comp (of_le hNO)).range.is_principal] (hgen : generator (ϕ.comp (of_le hNO)).range = 0) :
  N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  refine congr_arg coe (show (⟨x, hNO hx⟩ : O) = 0, from b.ext_elem (λ i, _)),
  rw (eq_bot_iff_generator_eq_zero _).mpr hgen at hϕ,
  rw [linear_equiv.map_zero, finsupp.zero_apply],
  exact (submodule.eq_bot_iff _).mp (hϕ ((finsupp.lapply i).comp b.repr) bot_le) _ ⟨⟨x, hx⟩, rfl⟩
end

-- Note that the converse may not hold if `ϕ` is not injective.
lemma generator_map_dvd_of_mem {N : submodule R M}
  (ϕ : M →ₗ[R] R) [(N.map ϕ).is_principal] {x : M} (hx : x ∈ N) :
  generator (N.map ϕ) ∣ ϕ x :=
by { rw [← mem_iff_generator_dvd, submodule.mem_map], exact ⟨x, hx, rfl⟩ }

-- Note that the converse may not hold if `ϕ` is not injective.
lemma generator_range_dvd_of_mem {N O : submodule R M} (hNO : N ≤ O)
  (ϕ : O →ₗ[R] R) [(ϕ.comp (of_le hNO)).range.is_principal] {x : M} (hx : x ∈ N) :
  generator (ϕ.comp (of_le hNO)).range ∣ ϕ ⟨x, hNO hx⟩ :=
by { rw [← mem_iff_generator_dvd, linear_map.mem_range], exact ⟨⟨x, hx⟩, rfl⟩ }

end comm_ring

section integral_domain

variables {ι : Type*} {R : Type*} [integral_domain R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

lemma not_mem_of_ortho {x : M} {N : submodule R M}
  (ortho : ∀ (c : R) (y ∈ N), c • x + y = (0 : M) → c = 0) :
  x ∉ N :=
by { intro hx, simpa using ortho (-1) x hx }

lemma ne_zero_of_ortho {x : M} {N : submodule R M}
  (ortho : ∀ (c : R) (y ∈ N), c • x + y = (0 : M) → c = 0) :
  x ≠ 0 :=
mt (λ h, show x ∈ N, from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)

/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def submodule.induction_on_rank_aux (b : basis ι R M) (P : submodule R M → Sort*)
  (ih : ∀ (N : submodule R M),
    (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') → P N)
  (n : ℕ) (N : submodule R M)
  (rank_le : ∀ {m : ℕ} (v : fin m → N),
    linear_independent R (coe ∘ v : fin m → M) → m ≤ n) :
  P N :=
begin
  haveI : decidable_eq M := classical.dec_eq M,
  have Pbot : P ⊥,
  { apply ih,
    intros N N_le x x_mem x_ortho,
    exfalso,
    simpa using x_ortho 1 0 N.zero_mem },

  induction n with n rank_ih generalizing N,
  { suffices : N = ⊥,
    { rwa this },
    apply eq_bot_of_rank_eq_zero b _ (λ m v hv, nat.le_zero_iff.mp (rank_le v hv)) },
  apply ih,
  intros N' N'_le x x_mem x_ortho,
  apply rank_ih,
  intros m v hli,
  refine nat.succ_le_succ_iff.mp (rank_le (fin.cons ⟨x, x_mem⟩ (λ i, ⟨v i, N'_le (v i).2⟩)) _),
  convert hli.fin_cons' x _ _,
  { ext i, refine fin.cases _ _ i; simp },
  { intros c y hcy,
    refine x_ortho c y (submodule.span_le.mpr _ y.2) hcy,
    rintros _ ⟨z, rfl⟩,
    exact (v z).2 }
end

/-- In an `n`-dimensional space, the rank is at most `m`. -/
lemma basis.card_le_card_of_linear_independent_aux
  {R : Type*} [integral_domain R]
  (n : ℕ) {m : ℕ} (v : fin m → fin n → R) :
  linear_independent R v → m ≤ n :=
begin
  revert m,
  refine nat.rec_on n _ _,
  { intros m v hv,
    cases m, { refl },
    exfalso,
    have : v 0 = 0,
    { ext i, exact fin_zero_elim i },
    have := hv.ne_zero 0,
    contradiction },
  intros n ih m v hv,
  cases m,
  { exact nat.zero_le _ },

  -- Induction: try deleting a dimension and a vector.
  suffices : ∃ (v' : fin m → fin n → R), linear_independent R v',
  { obtain ⟨v', hv'⟩ := this,
    exact nat.succ_le_succ (ih v' hv') },
  -- Either the `0`th dimension is irrelevant...
  by_cases this : linear_independent R (λ i, v i ∘ fin.succ),
  { exact ⟨_, this.comp fin.succ (fin.succ_injective _)⟩ },
  -- ... or we can write (x, 0, 0, ...) = ∑ i, c i • v i where c i ≠ 0 for some i.
  simp only [fintype.linear_independent_iff, not_forall, not_imp] at this,
  obtain ⟨c, hc, i, hi⟩ := this,
  have hc : ∀ (j : fin n), ∑ (i : fin m.succ), c i * v i j.succ = 0,
  { intro j,
    convert congr_fun hc j,
    rw [@finset.sum_apply (fin n) (λ _, R) _ _ _],
    simp },
  set x := ∑ i', c i' * v i' 0 with x_eq,
  -- We'll show each equation of the form (y, 0, 0, ...) = ∑ i', c' i' • v i' must have c' i ≠ 0.
  use λ i' j', v (i.succ_above i') j'.succ,
  rw fintype.linear_independent_iff at ⊢ hv,
  -- Assume that ∑ i, c' i • v i = (y, 0, 0, ...).
  intros c' hc' i',
  set y := ∑ i', c' i' * v (i.succ_above i') 0 with y_eq,
  have hc' : ∀ (j : fin n), (∑ (i' : fin m), c' i' * v (i.succ_above i') j.succ) = 0,
  { intro j,
    convert congr_fun hc' j,
    rw [@finset.sum_apply (fin n) (λ _, R) _ _ _],
    simp },
  -- Combine these equations to get a linear dependence on the full space.
  have : ∑ i', (y * c i' - x * (@fin.insert_nth _ (λ _, R) i 0 c') i') • v i' = 0,
  { simp only [sub_smul, mul_smul, finset.sum_sub_distrib, ← finset.smul_sum],
    ext j,
    rw [pi.zero_apply, @pi.sub_apply (fin n.succ) (λ _, R) _ _ _ _],
    simp only [finset.sum_apply, pi.smul_apply, smul_eq_mul, sub_eq_zero],
    symmetry,
    rw [fin.sum_univ_succ_above _ i, fin.insert_nth_apply_same, zero_mul, zero_add, mul_comm],
    simp only [fin.insert_nth_apply_succ_above],
    refine fin.cases _ _ j,
    { simp },
    { intro j,
      rw [hc', hc, zero_mul, mul_zero] } },
  have hyc := hv _ this i,
  simp only [fin.insert_nth_apply_same, mul_zero, sub_zero, mul_eq_zero] at hyc,
  -- Therefore, either `c i = 0` (which contradicts the assumption on `i`) or `y = 0`.
  have hy := hyc.resolve_right hi,
  -- If `y = 0`, then we can extend `c'` to a linear dependence on the full space,
  -- which implies `c'` is trivial.
  convert hv (@fin.insert_nth _ (λ _, R) i 0 c') _ (i.succ_above i'),
  { rw fin.insert_nth_apply_succ_above },
  ext j,
  -- After a bit of calculation, we find that `∑ i, c' i • v i = (y, 0, 0, ...) = 0` as promised.
  rw [@finset.sum_apply (fin n.succ) (λ _, R) _ _ _, pi.zero_apply],
  simp only [pi.smul_apply, smul_eq_mul],
  rw [fin.sum_univ_succ_above _ i, fin.insert_nth_apply_same, zero_mul, zero_add],
  simp only [fin.insert_nth_apply_succ_above],
  refine fin.cases _ _ j,
  { rw [← y_eq, hy] },
  { exact hc' },
end

lemma basis.card_le_card_of_linear_independent
  {R : Type*} [integral_domain R] [module R M]
  {ι : Type*} [fintype ι] (b : basis ι R M)
  {ι' : Type*} [fintype ι'] {v : ι' → M} (hv : linear_independent R v) :
  fintype.card ι' ≤ fintype.card ι :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq ι',
  let e := fintype.equiv_fin ι,
  let e' := fintype.equiv_fin ι',
  let b := b.reindex e,
  have hv := (linear_independent_equiv e'.symm).mpr hv,
  have hv := hv.map' _ b.equiv_fun.ker,
  exact basis.card_le_card_of_linear_independent_aux (fintype.card ι) _ hv,
end

lemma basis.card_le_card_of_submodule
  {R : Type*} [integral_domain R] [module R M] (N : submodule R M)
  {ι : Type*} [fintype ι] (b : basis ι R M)
  {ι' : Type*} [fintype ι'] (b' : basis ι' R N) :
  fintype.card ι' ≤ fintype.card ι :=
b.card_le_card_of_linear_independent (b'.linear_independent.map' N.subtype N.ker_subtype)

lemma basis.card_le_card_of_le
  {R : Type*} [integral_domain R] [module R M] {N O : submodule R M} (hNO : N ≤ O)
  {ι : Type*} [fintype ι] (b : basis ι R O)
  {ι' : Type*} [fintype ι'] (b' : basis ι' R N) :
  fintype.card ι' ≤ fintype.card ι :=
b.card_le_card_of_linear_independent
  (b'.linear_independent.map' (submodule.of_le hNO) (N.ker_of_le O _))

/-- If we have two bases on the same space, their indices are in bijection. -/
noncomputable def basis.index_equiv {R ι ι' : Type*} [integral_domain R] [module R M]
  [fintype ι] [fintype ι'] (b : basis ι R M) (b' : basis ι' R M) :
  ι ≃ ι' :=
(fintype.card_eq.mp (le_antisymm
  (b'.card_le_card_of_linear_independent b.linear_independent)
  (b.card_le_card_of_linear_independent b'.linear_independent))).some

/-- If `N` is a submodule in a free, finitely generated module,
do induction on adjoining a linear independent element to a submodule. -/
def submodule.induction_on_rank [fintype ι] (b : basis ι R M) (P : submodule R M → Sort*)
  (ih : ∀ (N : submodule R M),
    (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') →
    P N)
  (N : submodule R M) : P N :=
submodule.induction_on_rank_aux b P ih (fintype.card ι) N (λ s hs hli,
  by simpa using b.card_le_card_of_linear_independent hli)

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def basis.mk_fin_cons {n : ℕ} {N : submodule R M} (y : M) (b : basis (fin n) R N)
  (hli : ∀ (c : R) (x ∈ N), c • y + x = 0 → c = 0)
  (hsp : ∀ (z : M), ∃ (c : R), z + c • y ∈ N) :
  basis (fin (n + 1)) R M :=
have span_b : submodule.span R (set.range (N.subtype ∘ b)) = N,
{ rw [set.range_comp, submodule.span_image, b.span_eq, submodule.map_subtype_top] },
@basis.mk _ _ _ (fin.cons y (N.subtype ∘ b) : fin (n + 1) → M) _ _ _
  ((b.linear_independent.map' N.subtype (submodule.ker_subtype _)) .fin_cons' _ _ $
    by { rintros c ⟨x, hx⟩ hc, rw span_b at hx, exact hli c x hx hc })
  (eq_top_iff.mpr (λ x _,
    by { rw [fin.range_cons, submodule.mem_span_insert', span_b], exact hsp x }))

@[simp] lemma basis.coe_mk_fin_cons {n : ℕ} {N : submodule R M} (y : M) (b : basis (fin n) R N)
  (hli : ∀ (c : R) (x ∈ N), c • y + x = 0 → c = 0)
  (hsp : ∀ (z : M), ∃ (c : R), z + c • y ∈ N) :
  (basis.mk_fin_cons y b hli hsp : fin (n + 1) → M) = fin.cons y (coe ∘ b) :=
basis.coe_mk _ _

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def basis.mk_fin_cons_of_le {n : ℕ} {N O : submodule R M}
  (y : M) (yO : y ∈ O) (b : basis (fin n) R N) (hNO : N ≤ O)
  (hli : ∀ (c : R) (x ∈ N), c • y + x = 0 → c = 0)
  (hsp : ∀ (z ∈ O), ∃ (c : R), z + c • y ∈ N) :
  basis (fin (n + 1)) R O :=
basis.mk_fin_cons ⟨y, yO⟩ (b.map (submodule.comap_subtype_equiv_of_le hNO).symm)
  (λ c x hc hx, hli c x (submodule.mem_comap.mp hc) (congr_arg coe hx))
  (λ z, hsp z z.2)

@[simp] lemma basis.coe_mk_fin_cons_of_le {n : ℕ} {N O : submodule R M}
  (y : M) (yO : y ∈ O) (b : basis (fin n) R N) (hNO : N ≤ O)
  (hli : ∀ (c : R) (x ∈ N), c • y + x = 0 → c = 0)
  (hsp : ∀ (z ∈ O), ∃ (c : R), z + c • y ∈ N) :
  (basis.mk_fin_cons_of_le y yO b hNO hli hsp : fin (n + 1) → O) =
    fin.cons ⟨y, yO⟩ (submodule.of_le hNO ∘ b) :=
basis.coe_mk_fin_cons _ _ _ _

end integral_domain

section principal_ideal_domain

open submodule.is_principal set submodule

variables {ι : Type*} {R : Type*} [integral_domain R] [is_principal_ideal_ring R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

open_locale matrix

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def submodule.basis_of_pid {ι : Type*} [fintype ι]
  (b : basis ι R M) (N : submodule R M) :
  Σ (n : ℕ), basis (fin n) R N :=
begin
  haveI := classical.dec_eq M,
  refine N.induction_on_rank b _ _,
  intros N ih,

  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : ∃ ϕ : M →ₗ[R] R, ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ,
  { obtain ⟨P, P_eq, P_max⟩ := set_has_maximal_iff_noetherian.mpr
        (infer_instance : is_noetherian R R) _ (submodule.range_map_nonempty N),
    obtain ⟨ϕ, rfl⟩ := set.mem_range.mp P_eq,
    use ϕ,
    intros ψ hψ,
    exact P_max (N.map ψ) ⟨_, rfl⟩ hψ },
  let ϕ := this.some,
  have ϕ_max := this.some_spec,
  -- Since `N.map ϕ` is a `R`-submodule of the PID `R`, it is principal and generated by some `a`.
  have a_mem : generator (N.map ϕ) ∈ N.map ϕ := generator_mem _,

  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`
  by_cases N_bot : N = ⊥,
  { rw N_bot,
    exact ⟨0, basis.empty _⟩ },
  by_cases a_zero : generator (N.map ϕ) = 0,
  { have := eq_bot_of_generator_maximal_map_eq_zero b ϕ_max a_zero,
    contradiction },

  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  let y := a_mem.some,
  obtain ⟨y_mem, ϕy_eq⟩ := a_mem.some_spec,
  have ϕy_ne_zero := λ h, a_zero (ϕy_eq.symm.trans h),

  -- If `N'` is `ker (ϕ : N → R)`, it is smaller than `N` so by the induction hypothesis,
  -- it has a basis `bN'`.
  have N'_le_ker : (ϕ.ker ⊓ N) ≤ ϕ.ker := inf_le_left,
  have N'_le_N : (ϕ.ker ⊓ N) ≤ N := inf_le_right,
  -- Note that `y` is orthogonal to `N'`.
  have y_ortho_N' : ∀ (c : R) (z : M), z ∈ ϕ.ker ⊓ N → c • y + z = 0 → c = 0,
  { intros c x hx hc,
    have hx' : x ∈ ϕ.ker := (inf_le_left : _ ⊓ N ≤ _) hx,
    rw linear_map.mem_ker at hx',
    simpa [ϕy_ne_zero, hx'] using congr_arg ϕ hc },
  obtain ⟨nN', bN'⟩ := ih (ϕ.ker ⊓ N) N'_le_N y y_mem y_ortho_N',
  use nN'.succ,

  -- Extend `bN'` with `y`, we'll show it's linear independent and spans `N`.
  refine basis.mk_fin_cons_of_le y y_mem bN' N'_le_N y_ortho_N' _,
  intros x hx,
  obtain ⟨b, hb⟩ : _ ∣ ϕ x := generator_map_dvd_of_mem ϕ hx,
  refine ⟨-b, _⟩,
  refine submodule.mem_inf.mpr ⟨linear_map.mem_ker.mpr _, N.add_mem hx (N.smul_mem _ y_mem)⟩,
  rw [linear_map.map_add, linear_map.map_smul, hb, ϕy_eq, smul_eq_mul, mul_comm,
      ← neg_mul_eq_neg_mul, add_neg_eq_zero],
end

lemma submodule.basis_of_pid_bot {ι : Type*} [fintype ι] (b : basis ι R M) :
  submodule.basis_of_pid b ⊥ = ⟨0, basis.empty _⟩ :=
begin
  obtain ⟨n, b'⟩ := submodule.basis_of_pid b ⊥,
  let e : fin n ≃ fin 0 := b'.index_equiv (basis.empty _ : basis (fin 0) R (⊥ : submodule R M)),
  have : n = 0 := by simpa using fintype.card_eq.mpr ⟨e⟩,
  subst this,
  exact sigma.eq rfl (basis.eq_of_apply_eq $ fin_zero_elim)
end

/-- A submodule inside a free `R`-submodule of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def submodule.basis_of_pid_of_le {ι : Type*} [fintype ι]
  {N O : submodule R M} (hNO : N ≤ O) (b : basis ι R O) :
  Σ (n : ℕ), basis (fin n) R N :=
let ⟨n, bN'⟩ := submodule.basis_of_pid b (N.comap O.subtype)
in ⟨n, bN'.map (submodule.comap_subtype_equiv_of_le hNO)⟩

/-- A submodule inside the span of a linear independent family is a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def submodule.basis_of_pid_of_le_span
  {ι : Type*} [fintype ι] {b : ι → M} (hb : linear_independent R b)
  {N : submodule R M} (le : N ≤ submodule.span R (set.range b)) :
  Σ (n : ℕ), basis (fin n) R N :=
submodule.basis_of_pid_of_le le (basis.span hb)

variable {M}

/-- A finite type torsion free module over a PID is free. -/
noncomputable def module.free_of_finite_type_torsion_free [fintype ι] {s : ι → M}
  (hs : span R (range s) = ⊤) [no_zero_smul_divisors R M] :
  Σ (n : ℕ), basis (fin n) R M :=
begin
  classical,
  -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
  have := exists_maximal_independent R s,
  let I : set ι := this.some,
  obtain ⟨indepI : linear_independent R (s ∘ coe : I → M),
    hI : ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I)⟩ := this.some_spec,

  let N := span R (range $ (s ∘ coe : I → M)), -- same as `span R (s '' I)` but more convenient
  let sI : I → N := λ i, ⟨s i.1, subset_span (mem_range_self i)⟩, -- `s` restricted to `I`
  let sI_basis : basis I R N, -- `s` restricted to `I` is a basis of `N`
    from basis.span indepI,
  -- Our first goal is to build `A ≠ 0` such that `A • M ⊆ N`
  have exists_a : ∀ i : ι, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N,
  { intro i,
    by_cases hi : i ∈ I,
    { use [1, zero_ne_one.symm],
      rw one_smul,
      exact subset_span (mem_range_self (⟨i, hi⟩ : I)) },
    { simpa [image_eq_range s I] using hI i hi } },
  choose a ha ha' using exists_a,
  let A := ∏ i, a i,
  have hA : A ≠ 0,
  { rw finset.prod_ne_zero_iff,
    simpa using ha },
  -- `M ≃ A • M` because `M` is torsion free and `A ≠ 0`
  let φ : M →ₗ[R] M := linear_map.lsmul R M A,
  have : φ.ker = ⊥,
    from linear_map.ker_lsmul hA,
  let ψ : M ≃ₗ[R] φ.range := linear_equiv.of_injective φ this,
  have : φ.range ≤ N, -- as announced, `A • M ⊆ N`
  { suffices : ∀ i, φ (s i) ∈ N,
    { rw [linear_map.range_eq_map, ← hs, φ.map_span_le],
      rintros _ ⟨i, rfl⟩, apply this },
    intro i,
    calc (∏ j, a j) • s i = (∏ j in {i}ᶜ, a j) • a i • s i :
                                                 by rw [fintype.prod_eq_prod_compl_mul i, mul_smul]
                      ... ∈ N  : N.smul_mem _ (ha' i) },
  -- Since a submodule of a free `R`-module is free, we get that `A • M` is free
  obtain ⟨n, b : basis (fin n) R φ.range⟩ := submodule.basis_of_pid_of_le this sI_basis,
  -- hence `M` is free.
  exact ⟨n, b.map ψ.symm⟩
end

/-- A finite type torsion free module over a PID is free. -/
noncomputable def module.free_of_finite_type_torsion_free' [module.finite R M]
  [no_zero_smul_divisors R M] :
  Σ (n : ℕ), basis (fin n) R M :=
module.free_of_finite_type_torsion_free module.finite.exists_fin.some_spec.some_spec

.

open submodule.is_principal

lemma dvd_generator_iff {I : ideal R} [I.is_principal] {x : R} (hx : x ∈ I) :
  x ∣ generator I ↔ I = ideal.span {x} :=
begin
  conv_rhs { rw [← span_singleton_generator I] },
  erw [ideal.span_singleton_eq_span_singleton, ← dvd_dvd_iff_associated, ← mem_iff_generator_dvd],
  exact ⟨λ h, ⟨hx, h⟩, λ h, h.2⟩
end

@[simp] lemma fin.cast_le_succ {m n : ℕ} (h : (m + 1) ≤ (n + 1)) (i : fin m) :
  fin.cast_le h i.succ = (fin.cast_le (nat.succ_le_succ_iff.mp h) i).succ :=
by simp [fin.eq_iff_veq]

lemma generator_maximal_range_dvd {N O : submodule R M} (hNO : N ≤ O)
  {ϕ : O →ₗ[R] R} (hϕ : ∀ (ψ : O →ₗ[R] R), (ϕ.comp $ of_le hNO).range ≤ (ψ.comp $ of_le hNO).range →
    (ψ.comp $ of_le hNO).range = (ϕ.comp (of_le hNO)).range)
  [(ϕ.comp (of_le hNO)).range.is_principal]
  (y : M) (yN : y ∈ N) (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.comp (of_le hNO)).range)
  (ψ : O →ₗ[R] R) : generator (ϕ.comp (of_le hNO)).range ∣ ψ ⟨y, hNO yN⟩ :=
begin
  let a : R := generator (ϕ.comp (of_le hNO)).range,
  let d : R := is_principal.generator (submodule.span R {a, ψ ⟨y, hNO yN⟩}),
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp
    (subset_span (mem_insert _ _)),
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ := (mem_iff_generator_dvd _).mp
    (subset_span (mem_insert_of_mem _ (mem_singleton _))),
  refine dvd_trans _ d_dvd_right,
  rw [dvd_generator_iff, ideal.span,
      ← span_singleton_generator (submodule.span R {a, ψ ⟨y, hNO yN⟩})],
  obtain ⟨r₁, r₂, d_eq⟩ : ∃ r₁ r₂ : R, d = r₁ * a + r₂ * ψ ⟨y, hNO yN⟩,
  { obtain ⟨r₁, r₂', hr₂', hr₁⟩ := mem_span_insert.mp (is_principal.generator_mem
      (submodule.span R {a, ψ ⟨y, hNO yN⟩})),
    obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂',
    exact ⟨r₁, r₂, hr₁⟩ },
  let ψ' : O →ₗ[R] R := r₁ • ϕ + r₂ • ψ,
  have : span R {d} ≤ (ψ'.comp (of_le hNO)).range,
  { rw [span_le, singleton_subset_iff, set_like.mem_coe, linear_map.mem_range],
    refine ⟨⟨y, yN⟩, _⟩,
    change r₁ * ϕ ⟨y, hNO yN⟩ + r₂ * ψ ⟨y, hNO yN⟩ = d,
    rw [d_eq, ϕy_eq] },
  -- TODO: should be golfable
  refine le_antisymm _ (ideal.span_singleton_le_span_singleton.mpr d_dvd_left),
  refine le_trans this (le_of_eq _),
  rw span_singleton_generator,
  refine hϕ ψ' (le_trans _ this),
  rw [← span_singleton_generator (ϕ.comp (of_le hNO)).range],
  exact ideal.span_singleton_le_span_singleton.mpr d_dvd_left,
  { exact subset_span (mem_insert _ _) }
end

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix.

This is a strengthening of `submodule.basis_of_pid`.
-/
theorem submodule.exists_smith_normal_form {O : Type*} [add_comm_group O] [module R O]
  {ι : Type*} [fintype ι] (b : basis ι R O) (N : submodule R O) :
  ∃ (n : ℕ) (bO : basis ι R O) (bN : basis (fin n) R N) (f : fin n → ι) (a : fin n → R),
    ∀ i, (bN i : O) = a i • bO (f i) :=
begin
  suffices : ∀ (M : submodule R O) (N ≤ M),
    ∃ (m n : ℕ) (hnm : n ≤ m) (bM : basis (fin m) R M) (bN : basis (fin n) R N)
      (a : fin n → R),
      ∀ i, (bN i : O) = a i • bM (fin.cast_le hnm i),
  { obtain ⟨m, n, hnm, b', bN, a, h⟩ := this ⊤ N le_top,
    let b'' : basis _ R O := b'.map (linear_equiv.of_top _ rfl),
    refine ⟨n, b''.reindex (b''.index_equiv b), bN, b''.index_equiv b ∘ fin.cast_le hnm, a, _⟩,
    intros i,
    rw [h, function.comp_app, basis.reindex_apply, equiv.symm_apply_apply, basis.map_apply,
        linear_equiv.of_top_apply] },
  intros M,
  refine induction_on_rank b _ _ M,
  intros M ih N N_le_M,

  -- Make a few abbreviations.
  let b'M := submodule.basis_of_pid b M,
  let inc : N →ₗ[R] M := submodule.of_le N_le_M,

  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : ∃ ϕ : M →ₗ[R] R, ∀ (ψ : M →ₗ[R] R),
    (ϕ.comp inc).range ≤ (ψ.comp inc).range → (ψ.comp inc).range = (ϕ.comp inc).range,
  { obtain ⟨P, P_eq, P_max⟩ := set_has_maximal_iff_noetherian.mpr
        (infer_instance : is_noetherian R R) _
        (show (set.range (λ ψ : M →ₗ[R] R, (ψ.comp inc).range)).nonempty,
         from ⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩),
    obtain ⟨ϕ, rfl⟩ := set.mem_range.mp P_eq,
    use ϕ,
    intros ψ hψ,
    exact P_max _ ⟨_, rfl⟩ hψ },
  let ϕ := this.some,
  have ϕ_max := this.some_spec,
  -- Since the range of `ϕ` is a `R`-submodule of the PID `R`, it is principal and generated by some `a`.
  let a := generator (ϕ.comp inc).range,
  have a_mem : a ∈ (ϕ.comp inc).range := generator_mem _,

  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`.
  by_cases N_bot : N = ⊥,
  { subst N_bot,
    exact ⟨b'M.1, 0, nat.zero_le _, b'M.2, basis.empty _, 0, fin_zero_elim⟩ },
  by_cases a_zero : a = 0,
  { have := eq_bot_of_generator_maximal_range_eq_zero b'M.2 N_le_M ϕ_max a_zero,
    contradiction },

  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  have ϕy_eq := a_mem.some_spec,
  cases a_mem.some with y yN,
  have ϕy_eq : ϕ ⟨y, N_le_M yN⟩ = a := ϕy_eq,
  have ϕy_ne_zero : ϕ ⟨y, N_le_M yN⟩ ≠ 0 := λ h, a_zero (ϕy_eq.symm.trans h),
  -- Write `y` as `a • y'` for some `y'`.
  have hdvd : ∀ i, a ∣ b'M.2.coord i ⟨y, N_le_M yN⟩ :=
    λ i, generator_maximal_range_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.2.coord i),
  choose c hc using hdvd,
  let y' : O := ∑ i, c i • b'M.2 i,
  have y'M : y' ∈ M := M.sum_mem (λ i _, M.smul_mem (c i) (b'M.2 i).2),
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M.2 i :=
    subtype.ext (show y' = M.subtype _,
      by { simp only [linear_map.map_sum, linear_map.map_smul], refl }),
  have a_smul_y' : a • y' = y,
  { refine congr_arg coe (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩, from _),
    rw [← b'M.2.sum_repr ⟨y, N_le_M yN⟩, mk_y', finset.smul_sum],
    refine finset.sum_congr rfl (λ i _, _),
    rw [← mul_smul, ← hc], refl },

  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 := mul_left_cancel' a_zero
  (calc a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ : (ϕ.map_smul a ⟨y', y'M⟩).symm
                    ... = ϕ ⟨y, N_le_M yN⟩ : by simp only [a_smul_y']
                    ... = a : ϕy_eq
                    ... = a * 1 : (mul_one a).symm),
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by simpa only [ϕy'_eq] using one_ne_zero,

  -- `M' := ker (ϕ : M → R)` is smaller than `M` and `N' := ker (ϕ : N → R)` is smaller than `N`,
  -- so we can apply the induction hypothesis.
  let M' : submodule R O := ϕ.ker.map M.subtype,
  let N' : submodule R O := (ϕ.comp inc).ker.map N.subtype,
  have M'_le_M : M' ≤ M := M.map_subtype_le ϕ.ker,
  have N'_le_M' : N' ≤ M',
  { intros x hx,
    simp only [mem_map, linear_map.mem_ker] at hx ⊢,
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx,
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩ },
  have N'_le_N : N' ≤ N := N.map_subtype_le (ϕ.comp inc).ker,
  -- Note that `y'` is orthogonal to `M'`.
  have y'_ortho_M' : ∀ (c : R) z ∈ M', c • y' + z = 0 → c = 0,
  { intros c x xM' hc,
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := submodule.mem_map.mp xM',
    rw linear_map.mem_ker at hx',
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := subtype.coe_injective hc,
    simpa only [linear_map.map_add, linear_map.map_zero, linear_map.map_smul, smul_eq_mul, add_zero,
                mul_eq_zero, ϕy'_ne_zero, hx', or_false] using congr_arg ϕ hc' },
  obtain ⟨m', n', hm'n', bM', bN', a', h'⟩ := ih M' M'_le_M y' y'M y'_ortho_M' N' N'_le_M',
  refine ⟨m' + 1, n' + 1, nat.succ_le_succ hm'n', _, _, fin.cons a a', _⟩,

  -- Extend `bM` with `y'` and `bN` with `y`, we'll show they are linear independent
  -- and span `M` resp. `N`.
  { refine basis.mk_fin_cons_of_le y' y'M bM' M'_le_M y'_ortho_M' _,
    intros z zM,
    refine ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - (ϕ ⟨z, zM⟩) • ⟨y', y'M⟩, linear_map.mem_ker.mpr _, _⟩⟩,
    { rw [linear_map.map_sub, linear_map.map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self] },
    { rw [linear_map.map_sub, linear_map.map_smul, sub_eq_add_neg, neg_smul], refl } },
  { refine basis.mk_fin_cons_of_le y yN bN' N'_le_N _ _,
    { intros c z zN' hc,
      refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') _)).resolve_left a_zero,
      rw [mul_comm, mul_smul, a_smul_y', hc] },
    { intros z zN,
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ := generator_range_dvd_of_mem N_le_M ϕ zN,
      refine ⟨-b, submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, _, _⟩⟩,
      { refine linear_map.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0, from _),
        rw [linear_map.map_sub, linear_map.map_smul, hb, ϕy_eq, smul_eq_mul,
            mul_comm, sub_self] },
      { simp only [sub_eq_add_neg, neg_smul], refl } } },
  { intro i,
    rw [basis.coe_mk_fin_cons_of_le, basis.coe_mk_fin_cons_of_le],
    refine fin.cases _ (λ i, _) i,
    { simp only [fin.cons_zero, fin.cast_le_zero],
      exact a_smul_y'.symm },
    { rw fin.cast_le_succ, simp only [fin.cons_succ, coe_of_le, h' i] } }
end

.

end principal_ideal_domain

/-- A set of linearly independent vectors in a module `M` over a semiring `S` is also linearly
independent over a subring `R` of `K`. -/
lemma linear_independent.restrict_scalars_algebras {R S M ι : Type*} [comm_semiring R] [semiring S]
  [add_comm_monoid M] [algebra R S] [module R M] [module S M] [is_scalar_tower R S M]
  (hinj : function.injective (algebra_map R S)) {v : ι → M} (li : linear_independent S v) :
  linear_independent R v :=
linear_independent.restrict_scalars (by rwa algebra.algebra_map_eq_smul_one' at hinj) li
