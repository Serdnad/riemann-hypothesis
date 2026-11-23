module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle506
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SatInd
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Abstract

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem idem_map {π : Representation ℂ G V} {π' : Representation ℂ G W} (hπ : IsSmooth π) (hπ' : IsSmooth π')
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (π g v) = π' g (f v)) (v : V) :
    f (idem hπ hH v) = idem hπ' hH (f v) := by
  have hy : f (idem hπ hH v) ∈ fixed π' H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← hf, GlobalTheory.LGrp.mem_fixed.1 (idem_mem hπ hH v) k hk]
  have hk : v - idem hπ hH v ∈ twKer π H 1 := (idem_eq_zero_iff hπ hH).1 (by
    rw [map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self])
  have hle : twKer π H 1 ≤ (twKer π' H 1).comap f := Submodule.span_le.2 (by
    rintro _ ⟨u, z, rfl⟩
    exact Submodule.subset_span ⟨u, f z, by rw [map_sub, map_smul, hf]⟩)
  have h0 : idem hπ' hH (f (v - idem hπ hH v)) = 0 := (idem_eq_zero_iff hπ' hH).2 (hle hk)
  rw [map_sub, map_sub, idem_of_mem hπ' hH hy, sub_eq_zero] at h0
  exact h0.symm

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {U : ∀ a, Subgroup (Γ a)}

theorem idem_tprod (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCompact (U a : Set (Γ a)))
    (hC : IsCompact (Subgroup.pi Set.univ U : Set (∀ a, Γ a))) (x : ∀ a, X a) :
    idem (isSmooth_piTensor hs) hC (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun a => idem (hs a) (hc a) (x a) := by
  classical
  have hS := isSmooth_piTensor hs
  have h1 : ∀ (x : ∀ a, X a) (i : α) (y : X i),
      idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i (idem (hs i) (hc i) y))) =
        idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i y)) := fun x i y => by
    let l : X i →ₗ[ℂ] ⨂[ℂ] a, X a := idem hS hC ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
    have hk : twKer (ρ i) (U i) 1 ≤ LinearMap.ker l := Submodule.span_le.2 (by
      rintro _ ⟨u, z, rfl⟩
      show l _ = 0
      rw [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
      have hu : Pi.mulSingle i (u : Γ i) ∈ Subgroup.pi Set.univ U := fun a _ => by
        show (Pi.mulSingle i (u : Γ i) : ∀ a, Γ a) a ∈ U a
        by_cases e : a = i
        · subst e; simp
        · rw [Pi.mulSingle_eq_of_ne e]; exact one_mem _
      refine Eq.trans ?_ (idem_apply_mem hS hC hu (PiTensorProduct.tprod ℂ (Function.update x i z)))
      rw [piTensor_tprod]
      show idem hS hC (PiTensorProduct.tprod ℂ _) = _
      congr 2
      funext a
      by_cases e : a = i
      · subst e; simp
      · simp [e])
    have h2 : l (idem (hs i) (hc i) y - y) = 0 := hk ((idem_eq_zero_iff (hs i) (hc i)).1 (by
      rw [map_sub, idem_of_mem _ _ (idem_mem _ _ _), sub_self]))
    rwa [map_sub, sub_eq_zero] at h2
  have h2 : ∀ (x : ∀ a, X a) (s : Finset α),
      idem hS hC (PiTensorProduct.tprod ℂ (s.piecewise (fun a => idem (hs a) (hc a) (x a)) x)) =
        idem hS hC (PiTensorProduct.tprod ℂ x) := fun x s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, h1, ← ih, ← Finset.piecewise_eq_of_notMem s (fun a => idem (hs a) (hc a) (x a)) x hi,
        Function.update_eq_self]
  rw [← h2 x Finset.univ, Finset.piecewise_univ, idem_of_mem]
  refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
  rw [piTensor_tprod]
  congr 1
  funext a
  exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem _ _ _) _ (hg a trivial)

end Abstract

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSatVecGL_twist {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (s : ℂ) {z : ℂˣ} (hz : (z : ℂ) = (qV E w : ℂ) ^ (-s)) :
    IsSatVecGL w (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) x (B.map (· * z)) := by
  have hfix : x ∈ fixed (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) (KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by
      rw [twist_apply, detChar_apply, absPow_det_of_mem s hg, Units.val_one, one_smul]
      exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g hg
  refine ⟨hx.1, hfix, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  rw [GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ n (Ov E w) ϖ j c.out = 0
  · simp [hc]
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hc
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det c.out =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ hϖ0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change c.out.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hj]
    simp
  have e3 : absPow (w.adicCompletion E) s (Units.mk0 ϖ hϖ0) = z := Units.ext (by
    have : ordV E w ϖ = 1 := by
      rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v ϖ = _ from hϖ]; rfl
    rw [val_absPow_completion, hz, Units.val_mk0, this]
    simp)
  rw [twist_apply, detChar_apply, e2, map_mul, map_mul, absPow_det_of_mem s ha, absPow_det_of_mem s hb, map_pow, e3,
    one_mul, mul_one, smul_comm, Units.val_pow_eq_pow_val]

variable {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)

theorem isSatVecGL_multiProd {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)} (hs : ∀ a, IsSmooth (π a))
    {S : Fin c → Multiset ℂˣ} {x : ∀ a, X a} (hx : ∀ a, IsSatVecGL w (π a) (x a) (S a))
    {f : IndSp (stdBlocks N h) (piTensor π)} (hf : f ∈ fixed (multiProd (stdBlocks N h) π) (KGL w (n := n))) (h0 : f ≠ 0)
    {r : ℂ} (hr : f.1.1 1 = r • PiTensorProduct.tprod ℂ x) :
    IsSatVecGL w (multiProd (stdBlocks N h) π) f (∑ a, S a) := by
  have hKO : ∀ m, KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hf' := hf
  rw [hKO] at hf'
  choose Z iZ mZ R β l y hR hβ hyS h1 hl using fun a => exists_model (w := w) (hx a).2.2.1
  have hy : ∀ a, y a ∈ fixed (R a) (KO _ _) := fun a => hKO _ ▸ (hyS a).2.1
  obtain ⟨F, hF, hF1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor R) (x := PiTensorProduct.tprod ℂ y)
    fun g hg => by
      rw [piTensor_tprod]
      congr 1
      exact funext fun a => GlobalTheory.LGrp.mem_fixed.1 (hy a) _ (hg a)
  obtain ⟨Y, hYe, hY⟩ := exists_map_isSatVecGL h h1 hl hF hF1
  rw [funext hβ] at hY
  refine ⟨h0, hf, hY.2.2.1, fun ϖ hϖ j hj => ?_⟩
  have hϖ0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  have hT := Tj_mem_hecke (n := n) hϖ j
  have hK : IsCommensurated (KGL w (n := n)) := Final.GLintComm E w n
  have e1 := (map_heckeVec (ρ := multiProd (stdBlocks N h) R) hK hT Y hYe F).trans (hY.2.2.2 ϖ hϖ j hj)
  rw [hKO] at hT hK e1 ⊢
  have hp : ∀ q : GL (Fin n) (w.adicCompletion E) ⧸ KO (w.adicCompletion E) (Fin n),
      ∃ p : parab (w.adicCompletion E) (stdBlocks N h), ((p : GL (Fin n) (w.adicCompletion E)) : _ ⧸ KO _ _) = q :=
    fun q => by
      obtain ⟨p, hp, u, hu, e⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 q.out
      exact ⟨⟨p, hp⟩, (QuotientGroup.eq.2 (by simpa [e] using hu)).trans q.out_eq'⟩
  choose p hp using hp
  have hω : ∀ q a, ∃ t : ℂ, Tj ℂ n (Ov E w) ϖ j (p q) ≠ 0 →
      idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (π a (leviProj _ _ (p q) a) (x a)) = t • x a ∧
      idem (hR a) GlobalTheory.SplitFlip.isCompact_KO (R a (leviProj _ _ (p q) a) (y a)) = t • y a := fun q a => by
    by_cases hq : Tj ℂ n (Ov E w) ϖ j (p q) = 0
    · exact ⟨0, fun e => absurd hq e⟩
    obtain ⟨i1, i2⟩ := intM_of_Tj hϖ0 hϖ hq
    obtain ⟨l, hl, e⟩ := dosetInd_eq_Tj hϖ0 hϖ (g := leviProj _ _ (p q) a) (fun s t => i1 _ _) fun s t => by
      have := i2 (stdBlocks N h ⟨a, s⟩) (stdBlocks N h ⟨a, t⟩)
      rw [← Pi.inv_apply, ← map_inv]
      rw [Units.val_mul, tor_val, Matrix.diagonal_mul] at this ⊢
      exact this
    exact ⟨_, fun _ => ⟨idem_of_isSatVecGL (hs a) (hx a) hϖ hl e, idem_of_isSatVecGL (hR a) (hyS a) hϖ hl e⟩⟩
  choose ω hω using hω
  rw [heckeVec_multiProd _ hK hT hR hF (hF1.trans (one_smul ℂ _).symm) p hp ω (fun q hq a => (hω q a hq).2),
    map_smul] at e1
  rw [heckeVec_multiProd _ hK hT hs hf' hr p hp ω (fun q hq a => (hω q a hq).1), smul_left_injective ℂ hY.1 e1]

end Completion

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

namespace C

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

theorem hsum (r s : ℕ) : ∑ i, ![r, s] i = r + s := by simp [Fin.sum_univ_two]

abbrev eC (r s : ℕ) : (Σ i, Fin (![r, s] i)) ≃ Fin (r + s) := GlobalTheory.SmGL.stdBlocks ![r, s] (hsum r s)

theorem eC_zero (i : Fin r) : eC r s ⟨0, i⟩ = Fin.castAdd s i :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 0 i).trans (by simp))

theorem eC_one (j : Fin s) : eC r s ⟨1, j⟩ = Fin.natAdd r j :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 1 j).trans (by simp))

theorem lowLeft {p : GL (Fin (r + s)) (Cinf E)} (hp : p ∈ parab (Cinf E) (eC r s)) :
    ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (p : Matrix _ _ (Cinf E)) i j = 0 := by
  intro i j hi hj
  have h := GlobalTheory.SmGL.mem_parab_iff.1 hp 1 0 (show Fin s from ⟨i - r, by omega⟩) (show Fin r from ⟨j, hj⟩)
    (by decide)
  rw [eC_one, eC_zero] at h
  convert h using 2 <;> apply Fin.ext <;> simp; omega

theorem decomp (p : parab (Cinf E) (eC r s)) :
    ∃ (u : BlockIx (r + s) r → Cinf E) (m : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)),
      p.1 = unip u * lev (Cinf E) r s m :=
  IwaFin.exists_unip_mul_lev r s p.1 (lowLeft p.2) (lowLeft (inv_mem p.2))

theorem contDiff_cc : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (fun _ : Fin (r + s) => Cinf E) (Fin.castAdd s j)).comp
      (contDiff_apply ℝ (fun _ : Fin (r + s) => Fin (r + s) → Cinf E) (Fin.castAdd s i))

theorem contDiff_nn : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (fun _ : Fin (r + s) => Cinf E) (Fin.natAdd r j)).comp
      (contDiff_apply ℝ (fun _ : Fin (r + s) => Fin (r + s) → Cinf E) (Fin.natAdd r i))

end C

open C in
theorem exists_local (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    ∃ (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E))
      (κ : Lie E (r + s) → Kinf E (r + s)) (u : Lie E (r + s) → BlockIx (r + s) r → Cinf E),
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (κ y).1) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧ κ (oneL E (r + s)) = 1 ∧
      ∀ᶠ y in nhds (oneL E (r + s)), Matrix.of y = (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1 := by
  obtain ⟨p, k, hp, hk, hp1, hk1, hpk⟩ := GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa E ![r, s] (eC r s)
  choose u m hm using fun y => decomp (E := E) (p y)
  have e1 : ∀ y, toL (m y).1.val = (fun i j => toL (p y).1.val (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
    fun y => by
      funext i j
      change ((m y).1 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.castAdd s i) (Fin.castAdd s j)
      rw [hm y, unip_lev_cc]
  have e2 : ∀ y, toL (m y).2.val = (fun i j => toL (p y).1.val (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
    fun y => by
      funext i j
      change ((m y).2 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.natAdd r i) (Fin.natAdd r j)
      rw [hm y, unip_lev_nn]
  refine ⟨fun y => (m y).1, fun y => (m y).2, k, u, ?_, ?_, hk, ?_, ?_, hk1, ?_⟩
  · simp only [e1]
    exact contDiff_cc.contDiffAt.comp _ hp
  · simp only [e2]
    exact contDiff_nn.contDiffAt.comp _ hp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e1 (oneL E (r + s))) i) j
    change ((m _).1 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e2 (oneL E (r + s))) i) j
    change ((m _).2 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.natAdd_inj]
  · filter_upwards [hpk] with y hy
    rw [hy, hm y]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem chord_of : ExpTw → SqIntCrit → Chord := by
  intro hTw hSq E _ _ _ r s hr hs V c T lam hlam hT hp hb φ hφ k g
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hdR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hd
  unfold pE at hp
  push_cast at hp
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.left φ hφ k g m₂
    refine ⟨mulChi r (Model.absC E (-(c / (r * (Module.finrank ℚ E : ℂ))))) ψ₀, aut_tw haut _, ?_,
      fun m₁ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E r _ (aut_tw haut _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₁ h1 h2 c₁ hc₁
      have h3 := hexp r₁ h1 h2 _ (hTw E r ψ₀ _ haut r₁ h1 h2 c₁ hc₁)
      have h4 := hb r₁ h1 (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.left_eq _ _ _ _ _ hr.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.left_arith r s r₁ _ lam _ _ (by exact_mod_cast hr) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.right φ hφ k g m₁
    refine ⟨mulChi s (Model.absC E (-(-c / (s * (Module.finrank ℚ E : ℂ))))) ψ₀, aut_tw haut _, ?_,
      fun m₂ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E s _ (aut_tw haut _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₂ h1 h2 c₂ hc₂
      have h3 := hexp r₂ h1 h2 _ (hTw E s ψ₀ _ haut r₂ h1 h2 c₂ hc₂)
      have h4 := hb (r + r₂) (by omega) (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.right_eq _ _ _ _ _ hs.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.right_arith r s r₂ _ lam _ _ (by exact_mod_cast hs) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4

end PositivityTheory.Rg.Rs
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

open ParabolicProjection in
theorem proj_of (hP : Pr) (hT : SliceTens) (hI : IndMap) : Proj := by
  intro E _ _ _ r s _ _ V hV c z₁ z₂ T hTs hL2
  have hmem := hT E r s V hV c z₁ z₂ T hTs hL2
  obtain ⟨φ₀, hφ₀V, hφ₀⟩ := hTs.ne
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hTs.unipInv φ₀ hφ₀V)
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀V).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀
  obtain ⟨hst₁, hsep₁⟩ := hP E r
  obtain ⟨hst₂, hsep₂⟩ := hP E s

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw (A2 E r) z₁ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  obtain ⟨V₁, p₁, hV₁, hp₁V, hp₁e, hp₁0⟩ := hsep₁ χ₁ hχ₁ hχ₁0
  have hf₁ : twMap r z₁ p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r z₁ p₁ (mulChi r (Model.absC E z₁) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r z₁ p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw (A2 E s) z₂ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  obtain ⟨V₂, p₂, hV₂, hp₂V, hp₂e, hp₂0⟩ := hsep₂ χ₂ hχ₂ hχ₂0
  have hf₂ : twMap s z₂ p₂ (∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s z₂ p₂ (mulChi s (Model.absC E z₂) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s z₂ p₂) hf₂

  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI E r s V (tw (A2 E r) z₁) (tw (A2 E s) z₂) T (twMap r z₁ p₁) (twMap s z₂ p₂)
    hV.stable hV.aut (isStable_tw hst₁ z₁) (isStable_tw hst₂ z₂) hTs.equiv hmem (twMap_equiv hst₁ hp₁e)
    (twMap_equiv hst₂ hp₂e)
  refine ⟨V₁, V₂, hV₁, hV₂, T', fun φ hφ => ⟨hT'u φ hφ, fun k g => ?_⟩, inj_of_irred hV hT'e ⟨φ₀, hφ₀V, fun h => ?_⟩, hT'e⟩
  · obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r z₁ p₁ (ψ₁' i)).1 m.1 * (twMap s z₂ p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  · have e := hT's φ₀ hφ₀V k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.Rs

end
end
