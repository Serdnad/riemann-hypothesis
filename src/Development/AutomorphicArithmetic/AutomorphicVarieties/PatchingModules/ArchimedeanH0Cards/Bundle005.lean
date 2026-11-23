module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D D'' : Dat x.A (plOf G)) (_ : IsOd h x X D) (_ : IsOd h x X'' D'') (g : D.Hom D''), Function.Surjective g.f → (∀ u, UrAx l (L.Ju u)) → ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
  intro l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy
  have hs : ∀ w, Function.Surjective (g.fq w) := by
    intro w q
    obtain ⟨m, rfl⟩ := D''.surj w q
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨D.π w m, g.comm w m⟩
  have top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
    rintro w hw y'' ⟨-, Y, hY⟩
    obtain ⟨Y, rfl⟩ := hs _ Y
    refine ⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩
    rw [hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]
  rcases w with v | u
  · exact top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy
  · obtain ⟨hz, Y, hY⟩ := hy
    obtain ⟨-, k1, k2⟩ := odKill l L G G0 h n x X D o
    obtain ⟨-, -, k3⟩ := odKill l L G G0 h n x X'' D'' o''
    obtain ⟨y, a1, a2, a3⟩ := (hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u))
      (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))
    exact ⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩
end

section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem cont_of_ker {A Γ M : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module A M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation A Γ M)
    (hk : ∀ᶠ g in nhds (1 : Γ), ∀ m, ρ g m = m) : ContAction ρ := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, nhds_discrete M, Filter.tendsto_pure]
  have hg : ∀ᶠ g in nhds p.1, ∀ m, ρ g m = ρ p.1 m := by
    have ht : Filter.Tendsto (fun g => p.1⁻¹ * g) (nhds p.1) (nhds 1) := by
      simpa using (continuous_const_mul p.1⁻¹).tendsto p.1
    filter_upwards [ht.eventually hk] with g hg m
    calc ρ g m = ρ p.1 (ρ (p.1⁻¹ * g) m) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ p.1 m := by rw [hg m]
  have hm : ∀ᶠ q : Γ × M in nhds p, q.2 = p.2 := by
    have h0 : ∀ᶠ m in nhds p.2, m = p.2 := by
      rw [nhds_discrete, Filter.eventually_pure]
    exact (continuous_snd.tendsto p).eventually h0
  filter_upwards [(continuous_fst.tendsto p).eventually hg, hm] with q h1 h2
  rw [h1, h2]

private theorem ev_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) :
    ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g = 1 := by
  have key : ∀ a b : x.A, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries x.K) ^ m) a =
      Ideal.Quotient.mk _ b → algebraMap x.A X a = algebraMap x.A X b := by
    intro a b hab
    rw [Ideal.Quotient.eq, PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hab
    obtain ⟨c, hc⟩ := hab
    rw [← sub_eq_zero, ← map_sub, hc, map_mul, hm, zero_mul]
  have hij : ∀ i j : Fin n, ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g i j = (1 : Matrix (Fin n) (Fin n) X) i j := by
    intro i j
    have hl := x.cont i j m
    filter_upwards [(hl.isOpen_fiber _).mem_nhds (Set.mem_singleton _)] with g hg
    have hg' := key _ _ hg
    simp only [NP.ρX, Matrix.map_apply]
    rw [hg']
    simp [mat, Matrix.one_apply]
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hij i)] with g hg
  exact Matrix.ext hg

private theorem tri_X {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (g : F.Gv v) :
    (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v).BlockTriangular id := by
  intro i j hij
  have h := (x.tri v g).1 i j hij
  simp only [NP.wiX, NP.ρX, NP.wX, mat, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
  rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, ← Units.val_mul, ← Units.val_mul, h, map_zero]

private theorem w_wi {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  simp only [NP.wX, NP.wiX]
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

private def triSub {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n : ℕ}
    (V : Submodule A (Matrix (Fin n) (Fin n) X)) (a b : Matrix (Fin n) (Fin n) X) : Submodule A V where
  carrier := {Z | (a * (Z : Matrix (Fin n) (Fin n) X) * b).BlockTriangular id}
  zero_mem' := by
    intro i j _
    simp
  add_mem' := by
    intro Z Z' h h' i j hij
    have e1 := h hij
    have e2 := h' hij
    simp only [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, e1, e2, add_zero]
  smul_mem' := by
    intro c Z h i j hij
    have e1 := h hij
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, e1, smul_zero]

theorem UpperTheory.V.Pa.B2.odEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X], (∃ m : ℕ, algebraMap x.A X (x.t ^ m) = 0) → ∃ D : Dat x.A (plOf G), Nonempty (IsOd h x X D) := by
  intro l _ L G G0 h n x X _ _ _ hX
  obtain ⟨m, hm⟩ := hX
  obtain ⟨-, hok⟩ := okX l L G G0 h n x X 1
  obtain ⟨rep, hrep⟩ := adEx l G.frame x.A X n (fun g => x.ρX X (h.p₀ g))
    (fun g => algebraMap x.A X ((1 : G.Γ →* x.A) g)) (Od x.A X n x.a) hok
  have hact : ∀ (g : G.G₀) (Z : Od x.A X n x.a),
      ((rep g Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) =
        x.ρX X (h.p₀ g) * Z * x.ρX X (h.p₀ g⁻¹) := by
    intro g Z
    rw [hrep.1 g Z]
    simp
  have hc : ∀ Z : Od x.A X n x.a, ((rep G.c Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) = -(Z : Matrix (Fin n) (Fin n) X)ᵀ := by
    intro Z
    rw [hrep.2 Z]
    simp
  letI : TopologicalSpace (Od x.A X n x.a) := ⊥
  haveI : DiscreteTopology (Od x.A X n x.a) := ⟨rfl⟩
  haveI : Finite (Od x.A X n x.a) := inferInstance
  have hp : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hcont : ContAction rep := by
    apply cont_of_ker
    have E := ev_one x X m hm
    have E1 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g) = 1 := by
      have := (hp.tendsto 1).eventually (by simpa using E)
      exact this
    have E2 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g⁻¹) = 1 := by
      have ht : Filter.Tendsto (fun g : G.G₀ => g⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv.tendsto (1 : G.G₀))
      exact ht.eventually E1
    have E3 := E1.and E2
    rw [show (1 : G.G₀) = ⟨1, G.η.ker.one_mem⟩ from rfl, nhds_subtype_eq_comap, Filter.eventually_comap] at E3
    filter_upwards [E3, G.η_open.mem_nhds G.η.ker.one_mem] with g hg hker Z
    obtain ⟨h1, h2⟩ := hg ⟨g, hker⟩ rfl
    apply Subtype.ext
    have := hact ⟨g, hker⟩ Z
    rw [h1, h2, Matrix.one_mul, Matrix.mul_one] at this
    exact this
  let M : FRep x.A G.Γ := ⟨Od x.A X n x.a, rep, hcont⟩
  let N : (plOf G).ι → Submodule x.A M.X :=
    Sum.elim (fun v => triSub (Od x.A X n x.a) (x.wiX X v) (x.wX X v)) (fun _ => ⊥)
  have hN : ∀ (w : (plOf G).ι) (g : (plOf G).G w), N w ≤ Submodule.comap (M.ρ ((plOf G).φ w g)) (N w) := by
    intro w g
    cases w with
    | inl v =>
      change L.Gv v at g
      intro Z hZ
      have hZ' : (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id := hZ
      show (x.wiX X v * ((rep ((G.φ v g : G.G₀) : G.Γ) Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id
      have e1 : h.p₀ (G.φ v g) = G0.frame.φ v g := Subtype.ext (h.φ v g)
      have e2 : h.p₀ (G.φ v g)⁻¹ = G0.frame.φ v g⁻¹ := by
        rw [map_inv h.p₀, e1]
        exact (map_inv (G0.frame.φ v) g).symm
      rw [hact, e1, e2]
      have hww := w_wi x X v
      have heq : x.wiX X v * (x.ρX X (G0.frame.φ v g) * (Z : Matrix (Fin n) (Fin n) X) * x.ρX X (G0.frame.φ v g⁻¹)) * x.wX X v =
          (x.wiX X v * x.ρX X (G0.frame.φ v g) * x.wX X v) * (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v) *
            (x.wiX X v * x.ρX X (G0.frame.φ v g⁻¹) * x.wX X v) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul,
          ← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul]
      rw [heq]
      exact ((tri_X x X v g).mul hZ').mul (tri_X x X v g⁻¹)
    | inr u =>
      intro Z hZ
      have hZ0 : Z = 0 := (Submodule.mem_bot _).1 hZ
      simp [N, hZ0]
  refine ⟨Dat.ofSub (plOf G) M N hN, ⟨⟨LinearEquiv.refl _ _, fun g m => hact g m, fun m => hc m, ?_, ?_⟩⟩⟩
  · intro v m
    exact (Submodule.Quotient.mk_eq_zero (N (Sum.inl v)) (x := (m : M.X))).trans
      ⟨fun hb i j hij => hb hij, fun hb i j hij => hb i j hij⟩
  · intro u a b hab
    have hab' := (Submodule.Quotient.eq (N (Sum.inr u)) (x := (a : M.X)) (y := b)).1 hab
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hab')
end

section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.B2

section

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

def mk2 (P : Fin g → Matrix (Fin n) (Fin n) X) (Z : Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun a b => ⟨0, 0, fun j => P j a b, Z a b⟩

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (AddMonoidHom.mk' DD.a DD.add_a) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j :=
  map_sum (AddMonoidHom.mk' (fun d : DD X g => d.ep j) fun x y => DD.add_ep x y j) f s

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j :=
  map_sum (AddMonoidHom.mk' (fun d : DD X g => d.ep' j) fun x y => DD.add_ep' x y j) f s

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta :=
  map_sum (AddMonoidHom.mk' DD.eta DD.add_eta) f s

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

theorem epsPrimeEtaMatrix_add (P P' : Fin g → Matrix (Fin n) (Fin n) X) (Z Z') :
    mk2 P Z + mk2 P' Z' = mk2 (fun j => P j + P' j) (Z + Z') := by
  ext a b <;> simp [mk2]

theorem epsPrimeEtaMatrix_sub (P P' : Fin g → Matrix (Fin n) (Fin n) X) (Z Z') :
    mk2 P Z - mk2 P' Z' = mk2 (fun j => P j - P' j) (Z - Z') := by
  ext a b <;> simp [mk2, sub_eq_add_neg]

theorem epsPrimeEtaMatrix_smul (c : A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    c • mk2 P Z = mk2 (fun j => c • P j) (c • Z) := by
  ext a b <;> simp [mk2, Algebra.smul_def, alg_eq]

theorem neg_transpose_epsPrimeEtaMatrix (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    -(mk2 P Z)ᵀ = mk2 (fun j => -(P j)ᵀ) (-Zᵀ) := by
  ext a b <;> simp [mk2]

theorem epsPrimeEtaMatrix_apply_eq_zero_iff {P : Fin g → Matrix (Fin n) (Fin n) X} {Z} {a b} :
    mk2 P Z a b = 0 ↔ (∀ j, P j a b = 0) ∧ Z a b = 0 :=
  ⟨fun h => ⟨fun j => congrArg (fun d : DD X g => d.ep' j) h, congrArg DD.eta h⟩,
    fun h => DD.ext rfl rfl (funext h.1) h.2⟩

theorem epsPrimeEtaMatrix_injective_pair {P P' : Fin g → Matrix (Fin n) (Fin n) X} {Z Z'} (h : mk2 P Z = mk2 P' Z') : P = P' ∧ Z = Z' :=
  ⟨funext fun j => Matrix.ext fun a b => congrArg (fun M : Matrix (Fin n) (Fin n) (DD X g) => (M a b).ep' j) h,
    Matrix.ext fun a b => congrArg (fun M : Matrix (Fin n) (Fin n) (DD X g) => (M a b).eta) h⟩

theorem evenOddBlockMatrix_mem_adjointDeformSubspace {a : ℕ} {P : Fin g → Matrix (Fin n) (Fin n) X} {Z} (hP : ∀ j, P j ∈ Ev A X n a)
    (hZ : Z ∈ Od A X n a) : mk2 P Z ∈ W2 n A X g a := fun i j =>
  ⟨fun e => ⟨fun _ => rfl, fun _ => rfl, fun h => by simp at h, fun _ => (hZ i j).1 e⟩,
    fun e => ⟨fun _ => rfl, fun _ => rfl, fun _ => funext fun m => (hP m i j).2 e, fun h => by simp at h⟩⟩

theorem exists_evenOddBlock_decomposition_of_mem {a : ℕ} {M : Matrix (Fin n) (Fin n) (DD X g)} (h : M ∈ W2 n A X g a) :
    ∃ P Z, (∀ j, P j ∈ Ev A X n a) ∧ Z ∈ Od A X n a ∧ M = mk2 P Z := by
  refine ⟨fun j => M.map fun d => d.ep' j, M.map DD.eta, fun m i j => ⟨fun _ => trivial, fun e => ?_⟩,
    fun i j => ⟨fun e => ((h i j).1 e).2.2.2 rfl, fun _ => trivial⟩, Matrix.ext fun i j => ?_⟩
  · exact congrFun (((h i j).2 e).2.2.1 rfl) m
  · by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact DD.ext (((h i j).1 e).1 rfl) (((h i j).1 e).2.1 rfl) rfl rfl
    · exact DD.ext (((h i j).2 e).1 rfl) (((h i j).2 e).2.1 rfl) rfl rfl

theorem algebraMap_matrix_mul_epsPrimeEtaMatrix (M : Matrix (Fin n) (Fin n) A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    M.map (algebraMap A (DD X g)) * mk2 P Z =
      mk2 (fun j => M.map (algebraMap A X) * P j) (M.map (algebraMap A X) * Z) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

theorem epsPrimeEtaMatrix_mul_algebraMap_matrix (M : Matrix (Fin n) (Fin n) A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    mk2 P Z * M.map (algebraMap A (DD X g)) =
      mk2 (fun j => P j * M.map (algebraMap A X)) (Z * M.map (algebraMap A X)) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

theorem epM_mul_epsPrimeEtaMatrix (Y P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    DD.epM Y * mk2 P Z = mk2 (fun _ => 0) (∑ j, Y j * P j) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, Matrix.sum_apply]
  exact Finset.sum_comm

theorem epsPrimeEtaMatrix_mul_epM (Y P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    mk2 P Z * DD.epM Y = mk2 (fun _ => 0) (∑ j, P j * Y j) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, Matrix.sum_apply]
  exact Finset.sum_comm

private theorem ev_od {a : ℕ} {P Y : Matrix (Fin n) (Fin n) X} (hP : P ∈ Ev A X n a) (hY : Y ∈ Od A X n a) :
    Y * P - P * Y ∈ Od A X n a := by
  refine sub_mem (fun i j => ⟨fun e => ?_, fun _ => trivial⟩) (fun i j => ⟨fun e => ?_, fun _ => trivial⟩)
  · refine (Submodule.mem_bot A).2 ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
    · rw [(Submodule.mem_bot A).1 ((hY i c).1 h), zero_mul]
    · rw [(Submodule.mem_bot A).1 ((hP c j).2 (by tauto)), mul_zero]
  · refine (Submodule.mem_bot A).2 ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
    · rw [(Submodule.mem_bot A).1 ((hY c j).1 (by tauto)), mul_zero]
    · rw [(Submodule.mem_bot A).1 ((hP i c).2 h), zero_mul]

end

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]

theorem rho1_conj_block_matrix (g g' : F.G₀) (P : Fin k.g → Matrix (Fin n) (Fin n) X) (Z) :
    ∃ Z', k.ρ1 X g * mk2 P Z * k.ρ1 X g' = mk2 (fun j => x.ρX X g * P j * x.ρX X g') Z' := by
  simp only [Kap.ρ1, NP.ρX]
  rw [mul_assoc (1 + _), algebraMap_matrix_mul_epsPrimeEtaMatrix, add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, ← mul_assoc, mul_add, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_add, epsPrimeEtaMatrix_mul_algebraMap_matrix]
  simp only [add_zero]
  exact ⟨_, rfl⟩

theorem rho1_conj_block_zero (g g' : F.G₀) (Z) :
    k.ρ1 X g * mk2 (fun _ => 0) Z * k.ρ1 X g' = mk2 (fun _ => 0) (x.ρX X g * Z * x.ρX X g') := by
  simp only [Kap.ρ1, NP.ρX]
  rw [mul_assoc (1 + _), algebraMap_matrix_mul_epsPrimeEtaMatrix, add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, ← mul_assoc, mul_add, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_add, epsPrimeEtaMatrix_mul_algebraMap_matrix]
  simp

noncomputable def cmm (v : F.Vl) (P : Fin k.g → Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) X :=
  ∑ j, ((k.Y j v).map (algebraMap x.A X) * P j - P j * (k.Y j v).map (algebraMap x.A X))

theorem weyl_conj_block_matrix (v : F.Vl) (P : Fin k.g → Matrix (Fin n) (Fin n) X) (Z) :
    k.wi1 X v * mk2 P Z * k.w1 X v =
      mk2 (fun j => x.wiX X v * P j * x.wX X v) (x.wiX X v * (Z + cmm k X v P) * x.wX X v) := by
  simp only [Kap.w1, Kap.wi1, NP.wX, NP.wiX, cmm]
  rw [mul_assoc _ (1 + _), add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, mul_assoc, ← mul_assoc (mk2 _ _), mul_sub, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_sub, epsPrimeEtaMatrix_mul_algebraMap_matrix, algebraMap_matrix_mul_epsPrimeEtaMatrix]
  simp only [add_zero, sub_zero, Finset.sum_sub_distrib, mul_assoc, add_sub_assoc]

theorem cmm_mem (v : F.Vl) {P : Fin k.g → Matrix (Fin n) (Fin n) X} (hP : ∀ j, P j ∈ Ev x.A X n x.a) :
    cmm k X v P ∈ Od x.A X n x.a :=
  Submodule.sum_mem _ fun j _ => ev_od (hP j) fun a b => ⟨fun e => by
    have : k.Y j v a b = 0 := (k.Y_mem j v a b).1 e
    simp [this], fun _ => trivial⟩

theorem od_diag (v : F.Vl) {Z : Matrix (Fin n) (Fin n) X} (hZ : Z ∈ Od x.A X n x.a) (i : Fin n) :
    (x.wiX X v * Z * x.wX X v) i i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : decide ((b : ℕ) < x.a) = x.ty v i
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro a _
    by_cases ha : x.ty v i = decide ((a : ℕ) < x.a)
    · rw [(Submodule.mem_bot x.A).1 ((hZ a b).1 (by simpa using (hb.trans ha).symm)), mul_zero]
    · have := (tyCard l F n x v 0).2.2.2 i a ha
      simp only [NP.wiX, Matrix.map_apply, this, map_zero, zero_mul]
  · simp only [NP.wX, Matrix.map_apply, x.w_blk v b i hb, map_zero, mul_zero]

theorem isLocallyConstant_rho1_of_algebraMap_pow_eq_zero (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) : IsLocallyConstant (k.ρ1 X) := by
  have aux : ∀ f : F.G₀ → Matrix (Fin n) (Fin n) x.A,
      (∀ i j, AdicCont (Ideal.span {x.t}) fun g => f g i j) → ∀ (R : Type) [CommRing R] [Algebra x.A R],
      algebraMap x.A R (x.t ^ m) = 0 → ∀ g0, ∀ᶠ g in nhds g0, (f g).map (algebraMap x.A R) = (f g0).map (algebraMap x.A R) := by
    intro f hf R _ _ hR g0
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hf i j m).eventually_eq g0]
      with g hg
    refine Matrix.ext fun i j => ?_
    have h2 := Ideal.Quotient.eq.1 (hg i j)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
    obtain ⟨c, hc⟩ := h2
    have h3 := congrArg (algebraMap x.A R) hc
    rw [RingHom.map_sub, map_mul, hR, zero_mul, sub_eq_zero] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  filter_upwards [Filter.eventually_all.2 fun j => aux (k.κ j) (k.mem j).2.1 X hm g0,
    aux (mat x.ρ) (by rw [← PowerSeries.maximalIdeal_eq_span_X]; exact x.cont) (DD X k.g)
      (by rw [alg_eq, hm, map_zero]) g0] with g h1 h2
  simp only [Kap.ρ1, NP.ρX, h1, h2]

end UpperTheory.V.Pa.B2
end
