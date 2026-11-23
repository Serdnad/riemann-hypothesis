module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.HermitianLattices.Bundle001
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory

theorem latSum_reindex_of_le_sup (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D C As B : Submodule (𝓞 E) W) (f g : W → ℂ) (hCD : C ≤ D) (hB : ∀ t ∈ As, t ∈ B ↔ t ∈ C) (hD : D ≤ As ⊔ C)
    (hfg : ∀ x ∈ D, ∀ t ∈ As, t - x ∈ C → f x = g t) (hg : ∀ t ∈ As, t ∉ D → g t = 0) :
    latSum D C f = latSum As B g := by
  classical
  unfold latSum
  set r : (↥D ⧸ C.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap D.subtype)) with hr
  set s : (↥As ⧸ B.comap As.subtype) → ↥As :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap As.subtype)) with hs
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have hex : ∀ x : ↥D, ∃ t : ↥As, (t : W) - x ∈ C := by
    intro x
    obtain ⟨a, ha, c, hc, h⟩ := Submodule.mem_sup.1 (hD x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have : a - (x : W) = -c := by rw [← h]; abel
    simpa [this] using hc
  choose τ hτ using hex
  have keyA : ∀ t u : ↥As, (Submodule.Quotient.mk t : ↥As ⧸ B.comap As.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    exact hB _ (t - u).2
  have keyD : ∀ t u : ↥D, (Submodule.Quotient.mk t : ↥D ⧸ C.comap D.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  let φ : (↥D ⧸ C.comap D.subtype) → (↥As ⧸ B.comap As.subtype) := fun z => Submodule.Quotient.mk (τ (r z))
  have hφ : ∀ z, (s (φ z) : W) - r z ∈ C := by
    intro z
    have h1 : (s (φ z) : W) - τ (r z) ∈ C := (keyA _ _).1 (hs' _)
    have := C.add_mem h1 (hτ (r z))
    simpa using this
  have hinj : Function.Injective φ := by
    intro z w h
    rw [← hr' z, ← hr' w, keyD]
    have h1 := hφ z
    have h2 := hφ w
    rw [h] at h1
    have := C.sub_mem h2 h1
    simpa using this
  have e1 : ∑ᶠ z, f (r z : W) = ∑ᶠ z, (fun y => g (s y : W)) (φ z) :=
    finsum_congr fun z => hfg _ (r z).2 _ (s (φ z)).2 (hφ z)
  rw [e1, ← finsum_mem_range (f := fun y => g (s y : W)) hinj, ← finsum_mem_univ (fun y => g (s y : W))]
  apply finsum_mem_inter_support_eq'
  intro y hy
  simp only [Set.mem_univ, iff_true]
  have hyD : (s y : W) ∈ D := by
    by_contra h
    exact hy (hg _ (s y).2 h)
  refine ⟨Submodule.Quotient.mk ⟨_, hyD⟩, ?_⟩
  have h1 := hφ (Submodule.Quotient.mk ⟨_, hyD⟩)
  have h2 : (r (Submodule.Quotient.mk ⟨_, hyD⟩) : W) - s y ∈ C := (keyD _ ⟨_, hyD⟩).1 (hr' _)
  have h3 := C.add_mem h1 h2
  have h4 := (keyA (s (φ (Submodule.Quotient.mk ⟨_, hyD⟩))) (s y)).2 (by simpa using h3)
  rwa [hs', hs'] at h4

end GlobalTheory
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NarrowJetMoments

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Notions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}


variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

end Notions

section Closure

variable {p : ℕ} [Fact p.Prime]

variable {X : Fields} {a b : ℕ}

end Closure

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
  {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}

end Data

section Datum

variable {X : Fields} {a b : ℕ} {SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {T cA cB' : ℕ}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} {w : HeightOneSpectrum (𝓞 X.K)}

variable (A : Amb X)

end Datum

section Clause

variable {X : Fields} (A : Amb X) (Pr : Primes X) (u : Pr.Word) {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 X.K))
  (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) {a b : ℕ} (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E)))
  {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := a) (ST := Pr.vT u) (SG := SG)) (d' : DecoSet (E := X.E) (n := b) (ST := Pr.vT u) (SG := SG'))

end Clause

section Bad

variable {E : Type} [Field E] [NumberField E]

theorem notMem_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (P : HeightOneSpectrum (𝓞 E)) (hn : (n : 𝓞 E) ∈ P.asIdeal) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨x, y, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (x : 𝓞 E) * (m : 𝓞 E) + (y : 𝓞 E) * (n : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) e
  refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)

variable {X : Fields}

theorem conjP_ne_self_of_split (hX : X.Ok) {v : HeightOneSpectrum (𝓞 X.F)} (hs : SplitAt X.E v) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P.asIdeal.under (𝓞 X.F) = v.asIdeal) : conjPrime₂ P ≠ P := by
  intro hc
  have hne : GlobalTheory.MuConj.starAlg hX.star_F ≠ 1 := by
    intro h
    obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have : star x = x := congrArg (fun σ : X.E ≃ₐ[X.F] X.E => σ x) h
    show X.emb τ x = X.emb τ (star x)
    rw [this]
  have key : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal ≤ Q.asIdeal → Q = P := by
    intro Q hQ
    have hu : Q.under (𝓞 X.F) = P.under (𝓞 X.F) := by
      refine HeightOneSpectrum.ext ?_
      show Q.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)
      rw [hP]
      exact (v.isMaximal.eq_of_le (Q.under (𝓞 X.F)).isPrime.ne_top (Ideal.map_le_iff_le_comap.1 hQ)).symm
    rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.MuConj.starAlg hX.star_F) hX.rankE hne P Q).1 hu with h | h
    · exact h
    · rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h
      rw [← hc]
      ext y
      rw [mem_conjP]
      exact (h (cO X.E y) y (star_star (y : X.E)).symm).symm
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  exact hQ ((key Q (hm ▸ Ideal.mul_le_left)).trans (key Q' (hm ▸ Ideal.mul_le_right)).symm)

variable {Pr : Primes X}

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem mem_vGs_iff {P : HeightOneSpectrum (𝓞 X.E)} : P ∈ Pr.vGs ↔ ∃ i, P ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Finset.mem_union, Fin.exists_fin_two]

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : (Pr.g i : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs h)

theorem notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hg : ∀ i, l ≠ Pr.g i)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_coprime ((Nat.coprime_primes hl (hPr.g_prime i)).2 (hg i)) P (g_mem hPr hi)
  · exact notMem_of_mem_QE hsel h hl hS

theorem natCast_mem_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} :
    (n : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal ↔ (n : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast]

theorem conjP_notMem_rowSG (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : conjPrime₂ P ∉ rowSG Pr sel mu := by
  classical
  intro hP'
  rcases Finset.mem_union.1 hP with h | h <;> rcases Finset.mem_union.1 hP' with h' | h'
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    obtain ⟨j, hj⟩ := mem_vGs_iff.1 h'
    by_cases hij : i = j
    · subst hij
      have h1 : X.conjO (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hi
      have h2 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal :=
        (decoFin_mem_of_mem_divs hj : X.conjO (Pr.piG i) ∈ (conjPrime₂ P).asIdeal)
      rw [cO_cO] at h2
      obtain ⟨x, y, e⟩ := hPr.piG_cop i
      refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)
    · have hne : Pr.g i ≠ Pr.g j := by
        have := hPr.g_ne
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      exact notMem_of_coprime ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne) P
        (natCast_mem_conjP.1 (g_mem hPr hj)) (g_mem hPr hi)
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_mem_QE hsel h' (hPr.g_prime i) (hS i) (natCast_mem_conjP.2 (g_mem hPr hi))
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h'
    exact notMem_of_mem_QE hsel h (hPr.g_prime i) (hS i) (natCast_mem_conjP.1 (g_mem hPr hi))
  · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
    obtain ⟨v', -, e'⟩ := good_of_mem_QE h'
    have hvv : v' = v := by
      ext y
      rw [← hsel v, ← hsel v', e, e', Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP]
      have : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) y) = algebraMap (𝓞 X.F) (𝓞 X.E) y :=
        RingOfIntegers.ext (hX.star_F (y : X.F))
      rw [this]
    subst hvv
    exact conjP_ne_self_of_split hX hv.1 (e ▸ hsel v') (e'.symm.trans e)

end Bad

theorem mem_Sall {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
  classical
  unfold Sall
  rw [Finset.mem_union]

end GlobalTheory.Proof.NarrowJetMoments
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem int_mul_mem_lamOf (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, int_mul_mem_lamOf a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem qIntAll_of_latAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  intro D cc δ B h N N' L L' hA x hx
  have hsd := (h.1 N N' L L' hA).1
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hw := int_smul_mem_La L L' a hx
  rw [ha] at hw
  have hw' : StandardLatticesGL3.w0 D • x ∈ dualLat (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D B.tor L L') := by
    rw [hsd]; exact hw
  obtain ⟨m, hm⟩ := hw' x hx
  have him : (TaylorLogMetric.Hf D B.tor x x).im = 0 := by
    have : starRingEnd ℂ (TaylorLogMetric.Hf D B.tor x x) = TaylorLogMetric.Hf D B.tor x x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [TaylorLogMetric.Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]
    exact Complex.conj_eq_iff_im.1 this
  have h1 : (StandardLatticesGL3.w0 D).re = 1 / 2 := by simp [StandardLatticesGL3.w0]
  have h2 : (StandardLatticesGL3.w0 D).im = Real.sqrt D.host.d / 2 := by simp [StandardLatticesGL3.w0]
  have h3 : formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = TaylorLogMetric.Hf D B.tor x x := rfl
  refine ⟨m, ?_⟩
  rw [← hm, altE, LinearMap.map_smul₂, h3, smul_eq_mul, Complex.mul_im, h1, h2, him]
  ring

end GlobalTheory.ThetaMove
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Transport

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem opU_comp (e : V ≃ₗ[ℂ] V') {H : Sesq V} {H' : Sesq V'} (hH : ∀ x y, H' (e x) (e y) = H x y)
    (F : V' → ℂ) (x z : V) : opU H x (fun w => F (e w)) z = opU H' (e x) F (e z) := by
  simp only [opU, hH, map_add (f := _)]

def subEquiv (e : V ≃ₗ[ℂ] V') {Λ : AddSubgroup V} {Λ' : AddSubgroup V'} (h : ∀ x, x ∈ Λ ↔ e x ∈ Λ') : Λ ≃+ Λ' where
  toFun x := ⟨e x, (h _).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simp)⟩
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

def quotEquiv (e : V ≃ₗ[ℂ] V') {Λ₁ Λ₂ : AddSubgroup V} {Λ₁' Λ₂' : AddSubgroup V'} (h₁ : ∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁')
    (h₂ : ∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃+ (Λ₂' ⧸ Λ₁'.addSubgroupOf Λ₂') :=
  QuotientAddGroup.congr _ _ (subEquiv e h₂) (by
    ext y
    obtain ⟨x, rfl⟩ := (subEquiv e h₂).surjective y
    exact (AddSubgroup.mem_map_iff_mem (f := (subEquiv e h₂ : Λ₂ →+ Λ₂')) (subEquiv e h₂).injective).trans (h₁ _))

theorem term_add {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hd : IsSelfDual H A₂)
    (hs : IsSemiChar H A₂ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) {a s : V} (ha : a ∈ A₂) (hs₂ : s ∈ A₂)
    (hs₁ : s ∈ A₁) (z : V) : α (a + s) * opU H (a + s) F z = α a * opU H a F z := by
  rw [GlobalTheory.ThetaInter.alpha_opU_add hH hd hs ha hs₂, ← GlobalTheory.ThetaInter.opU_mul]
  congr 2
  funext w
  exact hF s hs₁ w

theorem inter_transport : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃ₗ[ℂ] V') (H : Sesq V) (H' : Sesq V') (α : V → ℂ) (α' : V' → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (Λ₁' Λ₂' : AddSubgroup V') (θ' : V' → ℂ), (∀ x y, H' (e x) (e y) = H x y) → (∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁') → (∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') → (∀ x ∈ Λ₂, α x = α' (e x)) → IsHerm H' → IsSelfDual H' Λ₂' → IsSemiChar H' Λ₂' α' → (IsSelfDual H Λ₂ ∧ IsSemiChar H Λ₂ α ∧ ∀ F' ∈ fixedBy H' α' Λ₂', (fun z => F' (e z)) ∈ fixedBy H α Λ₂) ∧ (θ' ∈ fixedBy H' α' Λ₁' → relIdx Λ₁' Λ₂' ≠ 0 → inter H α Λ₁ Λ₂ (fun z => θ' (e z)) = fun z => inter H' α' Λ₁' Λ₂' θ' (e z)) := by
  intro V V' _ _ _ _ e H H' α α' Λ₁ Λ₂ Λ₁' Λ₂' θ' hH h₁ h₂ hα hh hd hs
  have hE : ∀ x y, altE H x y = altE H' (e x) (e y) := fun x y => by simp only [altE, hH]
  refine ⟨⟨?_, ⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun F hF x hx z => ?_⟩, fun hθ _ => ?_⟩
  · ext x
    rw [h₂ x]
    conv_rhs => rw [← hd]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← hE]
      exact h y ((h₂ y).2 hy)
    · intro h y hy
      rw [hE]
      exact h _ ((h₂ y).1 hy)
  · rw [hα x hx]; exact hs.1 _ ((h₂ x).1 hx)
  · rw [hα _ (Λ₂.add_mem hx hy), hα x hx, hα y hy, map_add (f := _), hE]
    exact hs.2 _ ((h₂ x).1 hx) _ ((h₂ y).1 hy)
  · rw [opU_comp e hH, hα x hx]
    exact hF _ ((h₂ x).1 hx) _
  · funext z
    have hc : relIdx Λ₁ Λ₂ = relIdx Λ₁' Λ₂' := Nat.card_congr (quotEquiv e h₁ h₂).toEquiv
    rw [inter, inter, hc, ← finsum_comp_equiv (quotEquiv e h₁ h₂).toEquiv]
    congr 1
    refine finsum_congr fun c => ?_
    rw [opU_comp e hH, hα _ (Quotient.out c).2]
    have hm : -(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c) ∈
        Λ₁'.addSubgroupOf Λ₂' := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rfl
    have := term_add hh hd hs hθ (subEquiv e h₂ (Quotient.out c)).2
      (-(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c)).2
      (AddSubgroup.mem_addSubgroupOf.1 hm) (e z)
    rw [← AddSubgroup.coe_add, add_neg_cancel_left] at this
    exact this.symm

end GlobalTheory.ThetaMove.Transport
end
end
