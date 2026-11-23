module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle151
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevPin
open GlobalTheory.FinPl (idAt MxAt grpAt SplitPt)

variable {D : D7}

theorem idAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, P w → P' w) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mxAt_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {m n : ℕ} (w : Mx D m n)
    (h : IsHalf (q.e + cA D q.e) w) : MxAt P w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  refine idAt_mono (fun w (hw : w = q.v) => hw ▸ hP) (GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_)
  rw [← h2]
  exact h i j

theorem exists_fold (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) {ι : Type} (c : ι → WO S T →₀ ℂ)
    (hc : ∀ i, ∀ w ∈ (c i).support, MxAt P w) (l : List ι) : ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, MxAt P w) ∧
      ∀ f, comb ψ S T c' f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun w hw => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hw)
      exact fun i j => zero_mem _
    · rw [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul,
        GlobalTheory.MixPer.heisO_zero]
      rfl
  | cons i l ih =>
    obtain ⟨c', h1, h2⟩ := ih
    obtain ⟨c'', h3, h4⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c i) c'
    refine ⟨c'', fun w hw => ?_, fun f => by rw [h4, h2]; rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h3 w hw
    exact fun a b => add_mem (hc i x hx a b) (h1 y hy a b)

theorem mxAt_cast {F : ℕ → HSp D} {T : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {s j : ℕ} (h : s = j) (x : WO (F s) T →₀ ℂ)
    (hx : ∀ w ∈ x.support, MxAt P w) : ∀ w ∈ (cast (congrArg (fun n => WO (F n) T →₀ ℂ) h) x).support, MxAt P w := by
  subst h
  exact hx

def conjHom {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) :
    GL (Fin N) k →* GL Y k where
  toFun g := ⟨F.γ * g.val * F.β, F.γ * (g⁻¹).val * F.β, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc g.val,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, F.γβ], by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc (g⁻¹).val,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (1 : Matrix (Fin N) (Fin N) k) * F.β = 1
    rw [Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (g.val * h.val) * F.β = (F.γ * g.val * F.β) * (F.γ * h.val * F.β)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul])

theorem conj_iff {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y)
    (M : GL (Fin N) k) (x : GL Y k) : M.val = F.β * x.val * F.γ ↔ x = conjHom F M := by
  constructor
  · intro h
    refine Units.ext ?_
    change x.val = F.γ * M.val * F.β
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  · rintro rfl
    change M.val = F.β * (F.γ * M.val * F.β) * F.γ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) : Subgroup G :=
  J.comap ((conjHom F).comp ρ)

theorem mem_frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) (g : G) :
    g ∈ frameSub ρ F J ↔ ∀ x : GL Y k, (ρ g).val = F.β * x.val * F.γ → x ∈ J := by
  constructor
  · intro h x hx
    rw [(conj_iff F _ x).1 hx]
    exact h
  · intro h
    exact h _ ((conj_iff F _ _).2 rfl)

theorem under_inj {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hT : GlobalTheory.Core.Mi.IsTypePlaces Pg) {PP PP' : Formalism.L2.DIV.Pl D.host.E}
    (h : PP ∈ Pg) (h' : PP' ∈ Pg) (e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) : PP = PP' := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    have := hT.1 PP h
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using this
  obtain ⟨Q, _, hu⟩ := hT.2 _ hm
  exact (hu PP ⟨h, rfl⟩).trans (hu PP' ⟨h', e.symm⟩).symm

end GlobalTheory.LevPin

namespace GlobalTheory.LevPin

variable {D : D7}



theorem exists_locComb {a : XGeo D} {y : YRat a} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) {N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)} {β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)}
    {b : ∀ j, GA D (Yc D j)} {bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k}
    (Y : LocY l y N β b bas) (ν : Measure l.k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (eg : ∀ j, WO (Yc D j) (Yc D (j + 1)) →₀ ℂ) (egT : WO (Yc D (l.s + 1)) D.sp.X' →₀ ℂ)
      (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ),
      (∀ j a' (H : j + a' = l.s), (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) (eg j)
        ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      (ofSplit l.q).IsCombAt ψ (Y.FY (l.s + 1) 0 rfl) l.FT egT (S.T (Fin D.R.t)).PhiTop ∧
      (∀ j a' (H : j + 1 + a' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) (cg j)
        ((S.T (Fin D.R.t)).entry S.ψ ν j a' H 1 1)) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl) (cg l.s)
        (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX (l.s + 1) le_rfl) l.FM (cg (l.s + 1))
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) ∧
      (∀ j, ∀ w ∈ (eg j).support, IsHalf (l.q.e + cA D l.q.e) w) ∧ (∀ j, ∀ w ∈ (cg j).support, IsHalf (l.q.e + cA D l.q.e) w) := by
  have keyE : ∀ j, ∃ c : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ a' (H : j + a' = l.s),
      (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) c ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j ≤ l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY j (l.s - j + 1) (by omega))
        (Y.FY (j + 1) (l.s - j) (by omega)) ((S.T (Fin D.R.t)).Phi j (l.s - j) (by omega))
      refine ⟨c, fun a' H => ?_, hc.1⟩
      obtain rfl : a' = l.s - j := by omega
      exact hc
    · exact ⟨0, fun a' H => by omega, by simp⟩
  choose eg heg sEg using keyE
  obtain ⟨egT, hegT⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY (l.s + 1) 0 rfl) l.FT
    (S.T (Fin D.R.t)).PhiTop
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX (l.s + 1) le_rfl) l.FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have keyC : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = l.s → HEq c c₁) ∧ (j = l.s + 1 → HEq c c₂) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j < l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX j (by omega)) (l.FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j (l.s - j - 1) (by omega) 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega, hc.1⟩
      obtain rfl : c'' = l.s - j - 1 := by omega
      exact hc
    · by_cases h1 : j = l.s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega, h₁.1⟩
      · by_cases h2 : j = l.s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl, h₂.1⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim, by simp⟩
  choose cg k1 k2 k3 k4 using keyC
  refine ⟨eg, egT, cg, heg, hegT, k1, ?_, ?_, sEg, k4⟩
  · rw [eq_of_heq (k2 l.s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (l.s + 1) rfl)]; exact h₂

end GlobalTheory.LevPin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MeasCommon

open scoped ENNReal NNReal

theorem common_measure : ∀ (D : D7) (V : HSp D) (T : Type) (K : T → Subgroup (GL (Fin V.rank) (Lev.EAf D))) (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop), (∀ ρ m, good ρ m → m.IsHaarMeasure) → ∀ (μf : Measure (GfC V)), μf.IsHaarMeasure → ∀ (ν : T → Measure (GA D V)), (∀ t, Lev.IsMeasLevW V (K t) good (ν t)) → ∃ ν₀ : Measure (GA D V), ν₀.IsHaarMeasure ∧ ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 ∧ μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ ∧ μf {k | Lev.finE V k.1 ∈ K t} • ν t = ν₀ := by
  intro D V T K good hgood μf hμf ν hν
  haveI : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  obtain ⟨μR, μi, hR, hprod⟩ := GlobalTheory.T.exists_haar_adelicUnitary_product_real_finite D V μf hμf
  obtain ⟨hdec, hfin⟩ := GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D V
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨μR, hR, fun t => isEmptyElim t⟩
  obtain ⟨⟨θ, hθ⟩, hθall⟩ := (hν t₀).2
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := hAall A hA
  obtain ⟨B, hBm, hB0, hBT⟩ := GlobalTheory.T.exists_box_finite_pos_product_haar_unitaryGroups D.what₂.Tau (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) m
    (fun ρ => hgood ρ _ (hm ρ))
  haveI hνH : ∀ t, (ν t).IsHaarMeasure := fun t => (hν t).1
  let S : Set (GinfC V) := {a | ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) (a : GA D V)}
  have key : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) * (μi S * μf {k | Lev.finE V k.1 ∈ K t}) = ∏ ρ, m ρ (B ρ) := by
    intro t
    haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hbox := (((hν t).2.2 θ hθ).2 A hA).2 m hm B hBm
    have hset : {h : GA D V | Lev.finE V h ∈ K t ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} =
        {h | ∃ a ∈ S, ∃ k ∈ {k : GfC V | Lev.finE V k.1 ∈ K t}, h = (a : GA D V) * k} := by
      ext h
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨a, ha, k, hk, rfl⟩ := hdec h
        obtain ⟨e1, e2⟩ := hfin a ha k hk
        refine ⟨⟨a, ha⟩, fun ρ => ?_, ⟨k, hk⟩, ?_, rfl⟩
        · obtain ⟨b, hb, hb'⟩ := h2 ρ
          exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
        · show Lev.finE V k ∈ K t
          rw [← e1]; exact h1
      · rintro ⟨a, ha, k, hk, rfl⟩
        obtain ⟨e1, e2⟩ := hfin a.1 a.2 k.1 k.2
        refine ⟨by rw [e1]; exact hk, fun ρ => ?_⟩
        obtain ⟨b, hb, hb'⟩ := ha ρ
        exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
    rw [e, hset, Measure.smul_apply, hprod] at hbox
    rw [← hbox, ENNReal.smul_def, smul_eq_mul]
  have hc0 : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ 0 := fun t => by
    haveI : (ν t).IsHaarMeasure := (hν t).1
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure (ν t) μR).ne'
  have hcT : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ ⊤ := fun t => ENNReal.coe_ne_top
  have hX0 : μi S ≠ 0 := fun h0 => hB0 (by rw [← key t₀, h0, zero_mul, mul_zero])
  have hY0 : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 := fun t h0 => hB0 (by rw [← key t, h0, mul_zero, mul_zero])
  have hXT : μi S ≠ ⊤ := fun h0 => hBT (by rw [← key t₀, h0, ENNReal.top_mul (hY0 t₀), ENNReal.mul_top (hc0 t₀)])
  have hYT : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ := fun t h0 =>
    hBT (by rw [← key t, h0, ENNReal.mul_top hX0, ENNReal.mul_top (hc0 t)])
  refine ⟨((∏ ρ, m ρ (B ρ)) / μi S) • μR, ?_, fun t => ⟨hY0 t, hYT t, ?_⟩⟩
  · exact Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.2 ⟨hB0, hXT⟩).ne' (ENNReal.div_ne_top hBT hX0)
  · haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hv : μf {k | Lev.finE V k.1 ∈ K t} * ((ν t).haarScalarFactor μR : ℝ≥0∞) = (∏ ρ, m ρ (B ρ)) / μi S := by
      rw [ENNReal.eq_div_iff hX0 hXT, ← key t]
      ring
    rw [← hv]
    conv_lhs => rw [e]
    ext s _
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, mul_assoc]

noncomputable def volOf {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : Vol V :=
  ⟨μ, (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose, h,
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose_spec⟩

@[simp] theorem volOf_μ {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : (volOf μ h).μ = μ := rfl

theorem measures_common : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (b : ∀ j, GA D (Yc D j)), (∀ j, j ≤ D.R.m → (a.x j).Is) → ∃ m : YMeas y, GeoMeas (pk W) (mkGeo m b) ∧ (commOf (pk W) u (mkGeo m b)).VolLast := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y b _
  have hM : (pk W).IsModels := hP.bot.hyp.2.2.2.1.models
  have hm2 := D.R.two_le_m
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V =>
    (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have hf : ∀ j, ∃ μ : Measure (GfC (Yc D j)), μ.IsHaarMeasure := fun j =>
    (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).1
  choose μf hμf using hf
  obtain ⟨μT, hμT⟩ := (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D D.sp.X').1
  choose ρJ hρJ using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D (j + 1))).2 _ _ (y.jac j ρ h).d).1
  choose ρB hρB using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).2 _ _ (y.bes j ρ h).d).2 _ _ (y.bes j ρ h).o
  have hc : ∀ k, ∃ ν₀ : Measure (GA D (Yc D k)), ν₀.IsHaarMeasure ∧ (k < D.R.m → ∀ t,
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ 0 ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ ⊤ ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} •
        (pk W).νY t k = ν₀) := by
    intro k
    by_cases hk : k < D.R.m
    · have hw : ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D k).sig (tauE D ρ)).1 ((Yc D k).sig (tauE D ρ)).2) → Prop,
          (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧ ∀ t, Lev.IsMeasLevW (Yc D k)
            (Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)) good ((pk W).νY t k) := by
        by_cases hk' : k + 1 < D.R.m
        · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ h => h.1, fun t => (hM.νY t k hk').1⟩
        · obtain rfl : k = D.R.m - 1 := by omega
          exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ h => h.1, fun t => (hM.νY' t).1⟩
      obtain ⟨good, hg, hw⟩ := hw
      obtain ⟨ν₀, h1, h2⟩ := common_measure D (Yc D k) _ _ good hg (μf k) (hμf k) _ hw
      exact ⟨ν₀, h1, fun _ => h2⟩
    · exact ⟨_, (Classical.choice (GlobalTheory.Unf.VolExist.nonempty_vol (Yc D k))).haar, fun h => absurd h hk⟩
  choose ν₀ hν₀H hν₀ using hc
  obtain ⟨ν₀T, hν₀TH, hν₀T⟩ := common_measure D D.sp.X' _
    (fun t => Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t))
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1) μT hμT (fun t => (pk W).νX t)
    (fun t => (hM.νX t).1)
  have hLH : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).IsHaarMeasure :=
    fun j h => GlobalTheory.T.isHaarMeasure_map_emb0_of_rank_zero_decomposition D _ _ _ _ (a.x (j + 1)).vol.haar
  let vS : ∀ j, Vol (Yc D (j + 1)) := fun j => if h : j + 2 * 0 + 2 = D.R.m then volOf _ (hLH j h)
    else volOf (ν₀ (j + 1)) (hν₀H (j + 1))
  have hvS1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (vS j).μ = Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ := by
    intro j h; simp only [vS, dif_pos h, volOf_μ]
  have hvS2 : ∀ j, ¬ (j + 2 * 0 + 2 = D.R.m) → (vS j).μ = ν₀ (j + 1) := by
    intro j h; simp only [vS, dif_neg h, volOf_μ]
  let vol : ∀ k, Vol (Yc D k) := fun k => Nat.casesOn (motive := fun k => Vol (Yc D k)) k (volOf (ν₀ 0) (hν₀H 0)) vS
  let κ : ℕ → ℝ := fun k => Nat.casesOn (motive := fun _ => ℝ) k 1 fun j => if h : j + 2 * 0 + 2 = D.R.m then
    ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) else 1
  have hκ1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), κ (j + 1) =
      ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) := by
    intro j h; simp only [κ, dif_pos h]
  have hκ2 : ∀ k, k + 1 ≠ D.R.m → κ k = 1 := by
    intro k hk
    cases k with
    | zero => rfl
    | succ j => simp only [κ, dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)]
  have hκpos : ∀ k, 0 < κ k := by
    intro k
    by_cases hk : k + 1 = D.R.m
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h : j + 2 * 0 + 2 = D.R.m := by omega
      rw [hκ1 j h]
      haveI := hLH j h
      haveI := hν₀H (j + 1)
      exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
    · rw [hκ2 k hk]; exact one_pos
  have hset : ∀ k (β : GL (Fin (Yc D k).rank) (Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D k).rank),
      ({g : GfC (Yc D k) | g.1 ∈ levS _ β Ld} : Set (GfC (Yc D k))) =
        {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram β Ld} := by
    intro k β Ld; ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  refine ⟨⟨vol, volOf ν₀T hν₀TH, μf, μT, ρJ, ρB, κ⟩, ⟨hμf, hμT, hρJ, hρB, hκpos, ?_, ?_⟩, ?_⟩
  · intro t j hj
    have hX := hν₀ (j + 1) hj t
    show (vS j).μ = _
    rw [GlobalTheory.Fam.volLev, if_pos hj]
    change (vS j).μ = ENNReal.ofReal (κ (j + 1) * (μf (j + 1) {g | g.1 ∈ levS _ ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)}).toReal) • (pk W).νY t (j + 1)
    rw [hset]
    obtain ⟨hX0, hXT, hXe⟩ := hX
    generalize μf (j + 1) {g | Lev.finE (Yc D (j + 1)) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)} = X at hX0 hXT hXe ⊢
    by_cases hL : j + 2 * 0 + 2 = D.R.m
    · rw [hvS1 j hL, hκ1 j hL]
      haveI := hLH j hL
      haveI := hν₀H (j + 1)
      have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ) (ν₀ (j + 1))
      generalize (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) = c at e ⊢
      rw [e, ← hXe, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXT, mul_smul]
      ext s _
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
    · rw [hvS2 j hL, hκ2 (j + 1) (by omega), one_mul, ENNReal.ofReal_toReal hXT, hXe]
  · intro t
    obtain ⟨hX0, hXT, hXe⟩ := hν₀T t
    show ν₀T = _
    rw [GlobalTheory.Fam.volLev, if_neg (by omega)]
    change ν₀T = ENNReal.ofReal (κ D.R.m * (μT {k | k.1 ∈ levS _ (pk W).βX ((pk W).datXt t)}).toReal) • (pk W).νX t
    rw [hκ2 D.R.m (by omega), one_mul]
    have hs : {g : GfC D.sp.X' | g.1 ∈ levS _ (pk W).βX ((pk W).datXt t)} =
        {g | Lev.finE D.sp.X' g.1 ∈ Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t)} := by
      ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [hs, ENNReal.ofReal_toReal hXT, hXe]
  · intro j h
    exact hvS1 j h

end GlobalTheory.MeasCommon
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.PlaceSep

variable {D : D7}

theorem natCast_mem_of_under_eq {PP PP' : Pl D.host.E}
    (h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) {n : ℕ} (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  have h1 : ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  rw [h] at h1
  have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP'.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (u : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem twist_prime {gp : Fin 2 → ℕ} {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces gp Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ gp i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP hP
  refine ⟨q, hq, ?_, hne⟩
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, show Nat.card (𝓞 D.host.E ⧸ PP.asIdeal) = q from hc] at this

theorem g_mem_of_div (P : Formalism.L2.Host.PiBar D.host) {k : Fin 2} {w : Pl D.host.E} (hw : P.Div k w) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 := P.pb_over k
  rw [← hw] at h1
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at this

end GlobalTheory.Fam.PlaceSep


open GlobalTheory.Fam.PlaceSep in
theorem GlobalTheory.Fam.pg_qAll_under_inj : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ PP PP' : Pl D.host.E, (PP ∈ (pk W).Pg ∨ QAll W PP) → (PP' ∈ (pk W).Pg ∨ QAll W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro D L hT Gi Gl Kc Yd cX ex W hP PP PP' hPP hPP' hu
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev

  have mixed : ∀ A B : Pl D.host.E, A ∈ (pk W).Pg → QAll W B → A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → False := by
    intro A B hA hB hAB
    obtain ⟨k, hk⟩ := (hL.Pg A).1 hA
    obtain ⟨t, ht⟩ := hB
    obtain ⟨q, hq, hqB, hne⟩ := twist_prime (hL.Q_pl t) ht
    exact not_two_primes_mem B (D.host.g_prime k) hq (hne k).symm
      (natCast_mem_of_under_eq hAB (g_mem_of_div _ hk)) hqB
  rcases hPP with h1 | h1 <;> rcases hPP' with h2 | h2
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 h1
    obtain ⟨k', hk'⟩ := (hL.Pg PP').1 h2
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
    · exact e
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) (GlobalTheory.ProjLift.not_isConjPl_of_div _ hk' hk)
  · exact (mixed PP PP' h1 h2 hu).elim
  · exact (mixed PP' PP h2 h1 hu.symm).elim
  · exact hP.sel PP PP' h1 h2 hu
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedChain_datum_laws_under_levels : ∀ D : D7, LevelLawQ D := by
  first | exact @GlobalTheory.ChainTw.TwLaw.levelLawQ | exact GlobalTheory.ChainTw.TwLaw.levelLawQ | (intros; apply GlobalTheory.ChainTw.TwLaw.levelLawQ <;> assumption)
end
