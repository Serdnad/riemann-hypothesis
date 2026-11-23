module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle346
public import Mathlib.Topology.Algebra.Group.Units
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle234
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZero
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle276
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle466
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
public import Formalism.GelfandTransference.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle345
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.transpose_inverse_involution_apply : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k), thetaW k N (thetaW k N g) = g := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | exact GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.gelfand_kazhdan_contragredient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | exact GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra | (intros; apply GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

theorem _root_.GlobalTheory.T.interleaving_two_colour_embedding : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w → ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length) (σ₁ : Fin v.length ↪o Fin w.length), (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧ (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings | exact GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings | (intros; apply GlobalTheory.CompanionTheory.WordProd.Intl.interleave_embeddings <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem asmMult_main : AsmMult := by
  intro hL hU hR hS hE hQ h1 n _ _ μ _ E k k' val val' T T' hk hk'
  obtain ⟨m, c, w, g, ks, hb, hs, hv⟩ := hk
  obtain ⟨m', c', w', g', ks', hb', hs', hv'⟩ := hk'
  have hreg : ∀ i, KReg (ks i) := fun i => ⟨(hb i).2.1.continuousOn, (hb i).2.2.1⟩
  have hreg' : ∀ i, KReg (ks' i) := fun i => ⟨(hb' i).2.1.continuousOn, (hb' i).2.2.1⟩
  have hbp : ∀ p : Fin m × Fin m', IsBump (gconv (g p.1) (g' p.2)) (T + T') :=
    fun p => GlobalTheory.T.bump_convolution_support _ _ _ _ (hb p.1).1 (hb' p.2).1
  choose K hK using fun p : Fin m × Fin m' => h1 n μ E (w p.1 ++ w' p.2) (gconv (g p.1) (g' p.2)) (T + T') (hbp p)
  have hconv : ∀ y ∈ GLs n, conv μ E k k' y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [GlobalTheory.T.kernel_multiplier_linear hL n μ E c c' ks ks' k k' hreg hreg' hs hs' y hy, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.T.wave_kernel_convolution hL hU hR hS hE hQ n μ E (w i) (w' j) (g i) (g' j) T T' (ks i) (ks' j) (K (i, j))
      (hb i).1 (hb' j).1 (hb i).2 (hb' j).2 (hK (i, j)) y hy]
  have hconv' : ∀ y ∈ GLs n, conv μ E k' k y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [GlobalTheory.T.kernel_multiplier_linear hL n μ E c' c ks' ks k' k hreg' hreg hs' hs y hy, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hsw := GlobalTheory.T.wave_kernel_word_order_swap hS hR n μ E (w i) (w' j) _ (T + T') (K (i, j)) (hbp (i, j)) (hK (i, j))
    rw [gconv_comm] at hsw
    rw [GlobalTheory.T.wave_kernel_convolution hL hU hR hS hE hQ n μ E (w' j) (w i) (g' j) (g i) T' T (ks' j) (ks i) (K (i, j))
      (hb' j).1 (hb i).1 (hb' j).2 (hb i).2 hsw y hy, mul_comm]
  refine ⟨?_, fun y hy => by rw [hconv y hy, hconv' y hy], ?_,
    GlobalTheory.T.kernel_multiplier_on_eigenfunction hL n μ E k val T ⟨m, c, w, g, ks, hb, hs, hv⟩⟩
  · refine isMult_of_fintype μ E (fun p : Fin m × Fin m' => c p.1 * c' p.2) (fun p => w p.1 ++ w' p.2)
      (fun p => gconv (g p.1) (g' p.2)) K (fun p => ⟨hbp p, hK p⟩) hconv fun χ => ?_
    rw [Pi.mul_apply, hv χ, hv' χ, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [zVal_append, ← GlobalTheory.T.cosh_transform_convolution _ _ _ _ _ (hb i).1 (hb' j).1]
    ring
  · haveI := FiniteDimensional.complete ℂ E.V
    choose N d w₁ K₁ hK₁ hadj hval using fun i =>
      GlobalTheory.T.wave_kernel_decomposition hL hU hR hS hE hQ h1 n μ E (w i) (g i) T (ks i) (hb i).1 (hb i).2
    refine ⟨fun χ => ∑ q : (Σ i, Fin (N i)), (conj (c q.1) * d q.1 q.2) * zVal (w₁ q.1 q.2) χ * coshT (g q.1) (cas χ), ?_, ?_⟩
    · refine isMult_of_fintype μ E (fun q : (Σ i, Fin (N i)) => conj (c q.1) * d q.1 q.2) (fun q => w₁ q.1 q.2)
        (fun q => g q.1) (fun q => K₁ q.1 q.2) (fun q => ⟨(hb q.1).1, hK₁ q.1 q.2⟩) (fun y hy => ?_) fun χ => rfl

      rw [hs _ (inv_mem_GLs hy), map_sum, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hadj i y hy
      rw [map_smulₛₗ, this, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [smul_smul]
    · intro χ hχ

      rw [hv χ, map_sum]
      beta_reduce
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, GlobalTheory.T.cosh_transform_casimir_real n χ (g i) T hχ (hb i).1, hval i χ hχ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.phi_product_left_rank_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (i : ℕ) (τ : MRep k (i + 1)) (σ : GRep k 0) (h : (i + 1) + 0 = (i + 0) + 1), IsSmooth τ.ρ → IsSmooth σ.ρ → MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | exact GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.GLZero.phiN_prodPGn_zero <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegGenNu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_after {n : ℕ} (a : Fin n) :
    ∑ b ∈ Finset.univ.filter (fun b => a < b), 1 = (Fin.rev a : ℕ) := by
  have h : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
    ext b; simp
  rw [h]
  simp [Fin.val_rev]
  omega

theorem isLSeg_fine (G : Segment k) (a : Fin G.len) :
    IsLSeg (topCut G (fun _ => 1) (fun _ => one_pos) a) (dec G a).rep := by
  have hc : (dec G a).IsCusp := G.isCusp_term _
  have e : topCut G (fun _ => 1) (fun _ => one_pos) a = Segment.single (dec G a) hc := by
    refine Segment.ext_first ?_ rfl
    show G.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), 1 : ℕ) : ℂ) = G.first.nu ((Fin.rev a : ℕ) : ℂ)
    rw [card_after]
  rw [e]
  exact (single_spec hc).2.1

theorem exists_cut (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL (k := k)} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) :
    ∃ Γ : Fin G.len → Segment k, IsTopCut G' Γ ∧ ∀ a, IsLSeg (Γ a) (dec G a).rep := by
  have hd : ∑ a, (dec G a).1 = x.1 := (sum_dec G).trans h.deg_eq
  have hpos : ∀ a, 0 < (dec G a).1 := fun a => (G.isCusp_term _).1
  have h1 : jm (dec G) hd x.rep = 1 :=
    (hJ G x.rep h _ (dec G) hd hpos).1
      ⟨_, isTopCut_topCut G (fun _ => 1) (fun _ => one_pos) (by simp), isLSeg_fine G⟩
  by_contra hn
  have h0 := (hJ G' x.rep h' _ (dec G) hd hpos).2 hn
  rw [h1] at h0
  exact one_ne_zero h0

theorem card_le_len {G : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut G Γ) : s ≤ G.len := by
  rw [← h.1]
  calc s = ∑ _ : Fin s, 1 := by simp
    _ ≤ ∑ a, (Γ a).len := Finset.sum_le_sum fun a _ => (Γ a).len_pos

theorem first_eq (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL (k := k)} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) : G.first = G'.first := by
  obtain ⟨Γ, hΓ, hL⟩ := exists_cut hJ h h'
  obtain ⟨Γ', hΓ', -⟩ := exists_cut hJ h' h
  have hle := card_le_len hΓ
  have hle' := card_le_len hΓ'
  have hlen : G.len = G'.len := le_antisymm hle hle'
  have hpos := G.len_pos
  let l : Fin G.len := ⟨G.len - 1, by omega⟩
  have hl1 : (Γ l).len = 1 := by
    by_contra hne
    have h2 : 1 < (Γ l).len := by have := (Γ l).len_pos; omega
    have hlt : ∑ _ : Fin G.len, 1 < ∑ a, (Γ a).len :=
      Finset.sum_lt_sum (fun a _ => (Γ a).len_pos) ⟨l, Finset.mem_univ _, h2⟩
    rw [hΓ.1, ← hlen] at hlt
    simp at hlt
  have hb : below Γ l = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (l : ℕ) < b := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    have h4 := b.2
    have h5 : (l : ℕ) = G.len - 1 := rfl
    omega
  have hf : (Γ l).first = G'.first := by
    rw [hΓ.2 l, hb]
    simp
  have e : Γ l = Segment.single G'.first G'.isCusp_first := Segment.ext_first hf hl1
  have h6 : IsLSeg (Γ l) G'.first.rep := by
    rw [e]
    exact (single_spec _).2.1
  have h7 : dec G l = G.first := by
    have h8 : ((Fin.rev l : Fin G.len) : ℕ) = 0 := by
      simp only [Fin.val_rev, l]
      omega
    show G.first.nu (((Fin.rev l : Fin G.len) : ℕ) : ℂ) = G.first
    rw [h8]
    simp
  rw [← h7]
  exact eq_of_isLSeg (hL l) h6

theorem lSegGeneric_of_nuPair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (_hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJ : Zc.LSegJacquet k)
    (hP : GlobalTheory.BZSeg.NuPair k) : GlobalTheory.BZSeg.LSegGeneric k := by
  intro Δ N V _ _ π hπ
  by_contra hg
  obtain ⟨α, β, β', hd, hd', hα, hβ, hββ, h1, h2⟩ :=
    hP N V π hπ.hasSupport.isSmooth hπ.hasSupport.isIrreducible hg
  have hpos : ∀ a, 0 < (![α, β] a).1 := by
    intro a
    fin_cases a
    · exact hα
    · exact hβ
  have hpos' : ∀ a, 0 < (![β', α.nu 1] a).1 := by
    intro a
    fin_cases a
    · exact hββ ▸ hβ
    · exact hα
  have hcut : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![α, β] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![α, β] hd hpos).2 hn
    rw [h0] at h1
    simp at h1
  have hcut' : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![β', α.nu 1] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![β', α.nu 1] hd' hpos').2 hn
    rw [h0] at h2
    simp at h2
  obtain ⟨Γ, hΓ, hL⟩ := hcut
  obtain ⟨Γ', hΓ', hL'⟩ := hcut'
  have e1 : IsLSeg ((Γ 0).nu 1) (α.nu 1).rep := GlobalTheory.isLSeg_nu (hL 0) 1
  have e2 : IsLSeg (Γ' 1) (α.nu 1).rep := hL' 1
  have e3 : (Γ 0).first.nu 1 = (Γ' 1).first := first_eq hJ e1 e2
  have hb : below Γ' 1 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (1 : Fin 2) < b := (Finset.mem_filter.1 hb).2
    exact absurd h3 (by omega)
  rw [hΓ.2 0, hΓ'.2 1, hb, IrrGL.nu_nu] at e3
  have e4 : Δ.first.nu (((below Γ 0 + 1 : ℕ)) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    simpa using e3
  have e5 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 e4
  omega

end GlobalTheory.CompanionTheory.SegGenNu

end
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.interlacing_signature_parity : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), PositivityTheory.UnitaryDecomposition.Fits ε ε' e → Function.Injective (Sum.elim d d') → PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d' → (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧ ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | exact GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.similitude_invariance : Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassSimil.simil | exact GlobalTheory.CompanionTheory.SW.MassSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.MassSimil.simil <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.equidistribution : Equi := by
  first | exact @GlobalTheory.CompanionTheory.Equi.equi | exact GlobalTheory.CompanionTheory.Equi.equi | (intros; apply GlobalTheory.CompanionTheory.Equi.equi <;> assumption)
end

section

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem line_inverse {e : Mat n} {δ t s : ℂ} (he : e * e = δ • e) (hs : s * (1 + t * δ) = t) :
    (1 + t • e) * (1 - s • e) = 1 ∧ (1 - s • e) * (1 + t • e) = 1 := by
  have key : t - s - t * s * δ = 0 := by linear_combination -hs
  have key' : t - s - s * t * δ = 0 := by linear_combination -hs
  constructor
  · calc (1 + t • e) * (1 - s • e) = 1 + (t - s - t * s * δ) • e := by
          simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key, zero_smul, add_zero]
  · calc (1 - s • e) * (1 + t • e) = 1 + (t - s - s * t * δ) • e := by
          simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, he, smul_smul, sub_smul]
          abel
      _ = 1 := by rw [key', zero_smul, add_zero]

theorem conj_line {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    ∀ᶠ t : ℂ in 𝓝 0, Rm lam (1 + t • e) * XA lam B =
      (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e) := by
  have hc : ContinuousAt (fun t : ℂ => 1 + t * δ) 0 := by fun_prop
  have hδ : ∀ᶠ t : ℂ in 𝓝 0, 1 + t * δ ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [eventually_line_unit e, hδ] with t hu hne
  have hs : t / (1 + t * δ) * (1 + t * δ) = t := div_mul_cancel₀ t hne
  obtain ⟨-, hyx⟩ := line_inverse he hs
  have hB' : (1 + t • e) * B * (1 - (t / (1 + t * δ)) • e) =
      B + t • (e * B) + (-(t / (1 + t * δ))) • (B * e) + (-(t * (t / (1 + t * δ)))) • (e * B * e) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      mul_assoc]
    module
  have hcomm : (1 + t • e) * B = ((1 + t • e) * B * (1 - (t / (1 + t * δ)) • e)) * (1 + t • e) := by
    rw [mul_assoc ((1 + t • e) * B), hyx, mul_one]
  rw [conj_XA hD hu hcomm, hB', XA_add, XA_add, XA_add, XA_smul, XA_smul, XA_smul]

theorem comm_XA {lam : Fin n → ℤ} (hD : HolRm lam) {e : Mat n} (B : Mat n) {δ : ℂ} (he : e * e = δ • e) :
    XA lam e * XA lam B - XA lam B * XA lam e = XA lam (e * B) - XA lam (B * e) := by
  have hden : HasDerivAt (fun t : ℂ => 1 + t * δ) δ 0 := by
    simpa using ((hasDerivAt_id' (0:ℂ)).mul_const δ).const_add 1
  have hs : HasDerivAt (fun t : ℂ => t / (1 + t * δ)) 1 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).div hden (by simp)
    refine h.congr_deriv ?_
    simp
  have hts : HasDerivAt (fun t : ℂ => t * (t / (1 + t * δ))) 0 0 := by
    have h := (hasDerivAt_id' (0:ℂ)).mul hs
    refine h.congr_deriv ?_
    simp
  have hprod : ∀ (P Q : ℂ → Matrix (Jd n lam) (Jd n lam) ℂ) (P' Q' : Matrix (Jd n lam) (Jd n lam) ℂ),
      (∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0) → (∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0) →
      ∀ i j, HasDerivAt (fun t => (P t * Q t) i j) ((P' * Q 0 + P 0 * Q') i j) 0 := by
    intro P Q P' Q' hP hQ i j
    simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun k _ => (hP i k).mul (hQ k j)
  have hR : ∀ i k, HasDerivAt (fun t : ℂ => Rm lam (1 + t • e) i k) (XA lam e i k) 0 :=
    hasDerivAt_line hD e
  have hC : ∀ k j, HasDerivAt (fun _ : ℂ => XA lam B k j)
      ((0 : Matrix (Jd n lam) (Jd n lam) ℂ) k j) 0 := fun k j => by
    simpa using hasDerivAt_const (0:ℂ) (XA lam B k j)
  have hG : ∀ i k, HasDerivAt (fun t : ℂ => (XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) i k) ((XA lam (e * B) - XA lam (B * e)) i k) 0 := by
    intro i k
    have h := ((((hasDerivAt_id' (0:ℂ)).mul_const (XA lam (e * B) i k)).const_add (XA lam B i k)).add
      (hs.neg.mul_const (XA lam (B * e) i k))).add (hts.neg.mul_const (XA lam (e * B * e) i k))
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    exact h.congr_deriv (by ring)
  ext i j
  have hL := hprod (fun t => Rm lam (1 + t • e)) (fun _ => XA lam B) (XA lam e) 0 hR hC i j
  have hRt := hprod (fun t : ℂ => XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) (fun t => Rm lam (1 + t • e))
      (XA lam (e * B) - XA lam (B * e)) (XA lam e) hG hR i j
  have heq : (fun t : ℂ => (Rm lam (1 + t • e) * XA lam B) i j) =ᶠ[𝓝 0]
      (fun t : ℂ => ((XA lam B + t • XA lam (e * B) + (-(t / (1 + t * δ))) • XA lam (B * e)
        + (-(t * (t / (1 + t * δ)))) • XA lam (e * B * e)) * Rm lam (1 + t • e)) i j) := by
    filter_upwards [conj_line hD B he] with t ht
    exact congrArg (fun M => M i j) ht
  have huniq := hL.unique (hRt.congr_of_eventuallyEq heq)
  simp only [zero_smul, add_zero, Rm_one, mul_zero, mul_one, zero_div, neg_zero, zero_mul] at huniq
  rw [Matrix.sub_apply, huniq, Matrix.add_apply]
  ring

theorem XA_zero (lam : Fin n → ℤ) : XA lam (0 : Mat n) = 0 := by
  simpa using XA_smul lam (0 : ℂ) (0 : Mat n)

theorem xu_glRel : ∀ (n : ℕ) (lam : Fin n → ℤ), HolRm lam → Formalism.HadamardInequality.GlRel (Xu lam) := by
  intro n lam hD a b c d
  have hsq : (Matrix.single a b (1:ℂ) : Mat n) * Matrix.single a b 1 =
      (if b = a then (1:ℂ) else 0) • Matrix.single a b 1 := by
    by_cases h : b = a
    · subst h; rw [if_pos rfl, one_smul, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, zero_smul, Matrix.single_mul_single_of_ne _ _ _ _ h]
  have key := comm_XA hD (Matrix.single c d (1:ℂ)) hsq
  have hEB : XA lam ((Matrix.single a b (1:ℂ) : Mat n) * Matrix.single c d 1) =
      if b = c then XA lam (Matrix.single a d 1) else 0 := by
    by_cases h : b = c
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  have hBE : XA lam ((Matrix.single c d (1:ℂ) : Mat n) * Matrix.single a b 1) =
      if d = a then XA lam (Matrix.single c b 1) else 0 := by
    by_cases h : d = a
    · subst h; rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg h, Matrix.single_mul_single_of_ne _ _ _ _ h, XA_zero]
  simp only [Xu]
  rw [key, hEB, hBE]

end GlobalTheory.CompanionTheory.RmHol
end
end
