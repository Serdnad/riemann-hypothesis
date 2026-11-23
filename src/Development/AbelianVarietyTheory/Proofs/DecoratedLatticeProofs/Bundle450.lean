module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChiPowOfLevG
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle418
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle067
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TopInv

theorem multT_right {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (x : (⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) →ₗ[ℂ] GA D V → ℂ) (hx : x ∈ MultT θ M J χ)
    (v : ⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) : ∀ k ∈ J, ∀ g, x v (g * k) = χ k * x v g := by
  rw [mem_multT] at hx
  intro k hk g
  have key : ∀ T ∈ Mult θ M J χ, ∀ w, T w (g * k) = χ k * T w g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hT.lev w k hk g
    | zero => intro w; simp
    | add T T' _ _ h h' => intro w; simp [h, h', mul_add]
    | smul c T _ h => intro w; simp [h]; ring
  obtain ⟨T, rfl⟩ : ∃ T, x = PiTensorProduct.lift T := ⟨_, (PiTensorProduct.lift.apply_symm_apply x).symm⟩
  rw [LinearEquiv.symm_apply_apply] at hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w => simp [key _ hx w]; ring
  | add a b ha hb => simp [ha, hb, mul_add]

theorem rd_right {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.AdForm.rd_charts I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ0 * (A.h j b c * k0) * κ0 * κ.1 = γ0 * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd γ0 hγ0 c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

end GlobalTheory.AdForm.TopInv



theorem GlobalTheory.AdForm.TopInv.law_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  intro B X I hOk hP l Z u G _ _ Pl0 Tt F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hT bad K eW hRd heW hbT hLev htl n hn ψ hψ f v y β x κ hκ
  subst hn
  unfold PinChL at hCh
  have hm : (I.rec7 l Z).R.m ≤ B.R.m := le_rfl
  rw [hT.eT, trc_single_apply, trc_single_apply]
  have hκ' := (hT.lev κ).1 hκ
  obtain ⟨κ', hκ'm⟩ := (hLev.1 κ).1 hκ'
  have hchi := hLev.2 κ κ' hκ'm
  have hx := f.2
  dsimp only [CXP] at hx
  have hr := multT_right _ _ _ _ _ hx v
  have hf := hr _ hκ' (x * g.bT)
  have e : x * g.bT * (g.bT⁻¹ * κ * g.bT) = x * κ * g.bT := by group
  rw [e] at hf
  obtain ⟨hU, hchiU, hnorm⟩ := (GlobalTheory.AdForm.rd_emb_evz I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hT.emb bad K hRd (ι _ β)).1 (GlobalTheory.AdForm.LevChiTop.chi_pow_of_levG K hLev) κ κ' hκ'm
  have hψF : ψ ∈ (I.fm l u a).Fi _ := ((hCh.ram _ hm ψ).1 hψ).1.1
  have hemb : (g.oT _ rfl).emb (x * κ, 1) = (g.oT _ rfl).emb (x, 1) * ((g.oT _ rfl).emb.comp (MonoidHom.inl _ _)) κ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hq : ∀ z, k.rd (I.rec7 l Z).R.m β ψ y z = A.rd R.θ _ hm (ι _ β) ψ y z := fun z => congrFun (hCh.rdq _ hm β ψ y) z
  have hr2 : A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1) * ((g.oT (I.rec7 l Z).R.m rfl).emb.comp (MonoidHom.inl _ _)) κ) = ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1)) :=
    rd_right I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hm ψ hψF _ y _ ⟨_, hU⟩
  have hc : ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) = ((K.lev.chi κ' : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hchiU
  rw [hemb, hq, hq, hr2, hc, hf, hchi]
  have h1 : star ((K.lev.chi κ' : ℂˣ) : ℂ) * ((K.lev.chi κ' : ℂˣ) : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm]; simp
  linear_combination (ε * f.1 v (x * g.bT) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1))) * h1
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymReadEx
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem tame_step {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E} (hP : PP ∈ L.Pg)
    (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ}
    (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta j).1⁻¹ μ) : IsTame μ := by
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e1 : L.mu0 (i + 1) (idl q x) = 1 := res_idl q h (hL.mu0 ⟨i, h2⟩) (hL.chi ⟨i, h2⟩ PP hP) x hx
  have hr : IsRes L.C.eta PP 1 := fun z y v hy hv => by
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    have hzP : z ∉ PP.asIdeal := fun hm => v.ne_zero (hv.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
    rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := y)
      (by rw [hy]; exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP)]
    rfl
  have e2 : L.eta (idl q x) = 1 := res_idl q h hL.eta hr x hx
  have e3 : (Lift.chrStep L.mu0 L.eta (i + 1)).1 (idl q x) = 1 := by
    unfold Lift.chrStep
    split_ifs
    · change L.mu0 (i + 1) (idl q x) * (L.eta (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

theorem red_sym {D : D7} {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP)
    (S : SymData l.k l.s D.R.k) {π : Equiv.Perm (Fin D.R.r)} (hπ : IsSymOrd D.R.rS D.R.k π)
    (g g' : GL (Fin D.R.r) (kP PP)) (hg : ∀ i j, g'.val i j = g.val (π i) (π j)) :
    ((∃ x, l.Red S x g) ↔ g' ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧
    ∀ ψ₀ : AddChar (kP PP) ℂ,
      (∀ z, (S.ψ (((S.ϖ⁻¹ : l.kˣ) : l.k) * prO l.q z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z)) → ∀ x, l.Red S x g →
        (S.P.lam x : ℂ) = ψ₀ (edgeSum (symEdge D.R.rS D.R.k) g') := by
  have h1 := l.hs
  have h2 := S.odd
  have hρ : D.R.rS = S.ρ := by unfold Ranks.rS; omega
  let e : Fin D.R.k ⊕ Fin (l.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
  have hr : ∀ x, l.Red S x g ↔ ∀ a b z, Ideal.Quotient.mk PP.asIdeal z = g.val (e a) (e b) →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val a b - prO l.q z) < 1 := fun x =>
    ⟨fun h a b => h a b _ _ (he a) (he b), fun h a b a' b' ha hb => by
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      exact h a b⟩
  rw [hρ] at hπ ⊢
  simp only [hr]
  exact ⟨sym_grp S (prO l.q) (prO_le l.q l.idem) (prO_lt l.q l.idem) e he hπ g g' hg,
    fun ψ₀ h x hx => sym_chr S (prO l.q) e he hπ g g' hg ψ₀ h x hx⟩

theorem exists_symRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW _ a l
  obtain ⟨ψ₀, hψ₀, -, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hlev := W.Q.charW.base.lev
  have loc : ∀ PP : (pk W).Pg, ∃ S : SymData (l PP).k (l PP).s D.R.k, (ofSplit (l PP).q).IsChar (pk W).ψ S.ψ ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ (S.μ j)) ∧
      ∀ z, (S.ψ (((S.ϖ⁻¹ : (l PP).kˣ) : (l PP).k) * prO (l PP).q z) : ℂ) = ψ₀ PP.1 (Ideal.Quotient.mk _ z) := by
    intro PP
    obtain ⟨⟨ψk, hch, hcond⟩, -⟩ := GlobalTheory.WeilCondUnif.cond_unif W u hW a PP.1 (Or.inl PP.2) (l PP)
    obtain ⟨ϖ, hϖ, hres⟩ := exists_unif (l PP).q (l PP).idem hcond (hψ₀ PP.1 PP.2)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (l PP).s + 1 = 2 * ρ + 1 := by
      obtain ⟨b, hb⟩ := D.R.m_even
      have := (l PP).hs
      exact ⟨b - 1, by omega⟩
    obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel (l PP).k ψk hcond ϖ hϖ ρ D.R.k ((l PP).s + 1)
    choose μ hμ using fun j => GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (l PP).q) (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹
    refine ⟨⟨ψk, ϖ, ρ, P, fun j => if 1 ≤ j ∧ j ≤ D.R.m then μ j else 1, fun j => ?_, hcond, hϖ, hρ, hP'⟩, hch,
      fun j h1 h2 => ?_, hres⟩
    · split_ifs with h
      · exact tame_step (pk W).toLevCh hlev (l PP).q PP.2 (l PP).idem h.1 h.2 (hμ j)
      · exact fun _ _ => rfl
    · simp only [if_pos (And.intro h1 h2)]
      exact hμ j
  choose S h1 h2 h3 using loc
  refine ⟨S, h1, h2, fun x => (hH x).trans ?_, fun x hx y hxy => ?_⟩
  · exact ⟨fun h PP => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.2 (h PP (Set.mem_univ _)),
      fun h PP _ => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.1 (h PP)⟩
  · refine (hχ x hx ((hH _).1 hx)).trans ?_
    refine (map_prod (MonoidHom.eval _) _ _).trans (Finset.prod_congr rfl fun PP _ => Units.ext ?_)
    exact ((red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).2 _ (h3 PP) _ (hxy PP)).symm

end GlobalTheory.SymReadEx

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceFwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hint : ∀ a b, valuation k (g.val a b) ≤ 1)
    (h : ∀ a b, e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) : g ∈ colGroup k κ (Fin τ) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  let M : Matrix (XIx (Fin κ) (Fin τ) 0) (XIx (Fin κ) (Fin τ) 0) 𝒪[k] := Matrix.of fun a b => ⟨g.val a b, hint a b⟩
  have hM : ∀ a b, e b ≤ e a → (residue 𝒪[k]).mapMatrix M a b = (1 : Matrix _ _ 𝓀[k]) a b := fun a b hab => by
    have h1 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
      simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
    rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ?_
    convert h a b hab using 2
    simp only [M, Matrix.one_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hdet : ((residue 𝒪[k]).mapMatrix M).det = 1 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm, Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      rw [Matrix.submatrix_apply, hM _ _ le_rfl, Matrix.one_apply_eq]
    · intro i j hij
      have hij' : j < i := hij
      rw [Matrix.submatrix_apply, hM _ _ (by simpa using hij'.le), Matrix.one_apply_ne (e.symm.injective.ne hij'.ne')]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← residue_ne_zero_iff_isUnit, RingHom.map_det, hdet]
    exact one_ne_zero
  refine ⟨_, ⟨hu.unit, Units.ext ?_, rfl⟩, fun a b hab => ?_⟩
  · ext a b
    rfl
  · rw [hp, hp] at hab
    exact hM a b hab

theorem embX_mem {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : g ∈ colGroup k κ (Fin τ)) :
    embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  exact (h2 g hg).1



theorem colGroup_of_red {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : GL (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A.1)
    (hU : A ∈ Formalism.L2.Col.uniUT n _ κ []) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : (mt V x).map q.pr = F.β * g.val * F.γ) : g ∈ colGroup k κ (Fin τ) := by
  subst hr
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  refine mem_colGroup e he g (fun a b => ?_) fun a b hab => ?_
  · have := (valuation k).map_add_le (hM (e a) (e b)).le (LevelTest.val_le_one q (R (e a) (e b)))
    rwa [sub_add_cancel, ← hgM] at this
  · obtain ⟨-, h1, h2⟩ := Formalism.L2.Col.mem_uniUT.1 hU
    have ha : (e a).val < κ := hn ▸ (e a).2
    rcases hab.eq_or_lt with h | h
    · obtain rfl : b = a := e.injective h
      have h3 : R (e b) (e b) - 1 ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq, hR, h2 _ ha, map_one]
      have := (valuation k).map_add_lt (hM (e b) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [← hgM] at this
      simpa using this
    · have h3 : R (e a) (e b) ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hR, h1 _ _ ha h]
      have := (valuation k).map_add_lt (hM (e a) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [sub_add_cancel, ← hgM] at this
      rwa [Matrix.one_apply_ne (fun h' : a = b => h.ne' (congrArg e h')), sub_zero]

end Loc

theorem exists_red {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J T f bad) {y : (I.stp u I.mu0 0).Cl → TC.GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → TC.GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => S.Lb) (fun _ => S.U) (fun _ => S.chi) y st k) (x : S.U)
    (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ A : GL (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.asIdeal), A ∈ Formalism.L2.Col.uniUT (B.R.N 0) _ B.R.k [] ∧ LevRead.IsRed w x.1 A.1 := by
  subst hJ
  obtain ⟨h, h1, h2, -⟩ := TC.GLev0.chi_prod I S hR hI x
  exact ⟨_, inv_mem (h1 ⟨w, hw⟩), h2 ⟨w, hw⟩⟩


end GlobalTheory.FamTrace.TraceFwd

end
end

section

noncomputable section

section Col

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.LevRead Matrix
open scoped TensorProduct

namespace GlobalTheory.FamTraceChiCol.ColRead

theorem lamJ_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {gp : Fin 2 → ℕ} (G : Formalism.L2.Forms.GLoc F E σ gp) (i : Fin 2) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    {w : HeightOneSpectrum (𝓞 E)} (ρ : 𝓞 E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv F v)
    (hres : ∀ (z : AfE F E) (c : 𝓞 E ⧸ w.asIdeal), HasRes w (adAt F w z) c →
        ∃ hh : G.phi i v h (prV (E := E) v z) ∈ v.adicCompletionIntegers F,
          IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hh⟩ = ρ c)
    {xa : GL (Fin n) (AfE F E)} {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)} (hA : IsRed w xa A)
    (χ : ℕ → MulChar (Formalism.L2.Forms.kv F v) ℂ) (k t : ℕ) (z : 𝓞 E)
    (hz : Ideal.Quotient.mk w.asIdeal z =
      ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < k ∧ (y : ℕ) ≠ k then A x y else 0)
    (fr : GL (Fin n) (v.adicCompletion F)) (hfr : fr = 1) :
    ∃ w' : v.adicCompletionIntegers F, (w' : v.adicCompletion F) = G.phi i v h ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∧
      Formalism.L2.Forms.lamJ (G.psi0 i v h) χ k t 0 k (Formalism.L2.Forms.redM F v (G.mat i v h fr (bc (prV (E := E) v) xa))) =
        G.psi0 i v h (IsLocalRing.residue _ w') := by
  subst hfr
  obtain ⟨hh, e⟩ := hres (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z : E)) _ (by rw [adAt_inclE]; exact hasRes_coe w z)
  refine ⟨⟨_, hh⟩, rfl, ?_⟩

  rw [e, TC.GLev0.redM_mat G i h ρ hres hA, Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one, hz, map_sum ρ]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)

  rw [map_sum ρ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [apply_ite ρ, map_zero]
  rfl

end GlobalTheory.FamTraceChiCol.ColRead

end Col

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.FamTraceChiCol.ColRead

open GlobalTheory.SymBridge GlobalTheory.RootEx



theorem exists_close {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : Matrix (Fin n) (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A)
    (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : (mt V x).map q.pr = F.β * g.val * F.γ) :
    ∃ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z =
        (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) + 1 = b ∧ (b : ℕ) < κ ∧ (b : ℕ) ≠ κ then A a b else 0) ∧
      valuation k ((∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then g.val (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b)) else 0) -
        (ofSplit q).pr (z : D.host.E)) < 1 := by
  subst hr
  subst hn
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  have he' : ∀ a : Fin V.rank, e (Sum.inl (Sum.inl a)) = a := fun a => Fin.ext (he _)
  have hc : ∀ a b : Fin V.rank, ((a : ℕ) + 1 = b ∧ (b : ℕ) < V.rank ∧ (b : ℕ) ≠ V.rank) ↔ b.val = a.val + 1 := fun a b =>
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, b.2, b.2.ne⟩⟩
  refine ⟨∑ a : Fin V.rank, ∑ b : Fin V.rank, if b.val = a.val + 1 then R a b else 0, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [apply_ite (Ideal.Quotient.mk PP.asIdeal), map_zero, hR]
    exact if_congr (hc a b).symm rfl rfl
  · let φ : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)
    have hφ : ∀ r : 𝓞 D.host.E, (ofSplit q).pr (r : D.host.E) = φ r := fun _ => rfl

    rw [hφ, map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun a _ => ?_

    rw [map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun b _ => ?_
    split_ifs
    · rw [hgM, he', he']
      exact hM a b
    · rw [map_zero, sub_zero, map_zero]
      exact zero_lt_one

end GlobalTheory.FamTraceChiCol.ColRead

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.flatMap_besselToFourierJacobi_localModel : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  first | exact @GlobalTheory.FlatBFLoc.flatBF_of_laws | exact GlobalTheory.FlatBFLoc.flatBF_of_laws | (intros; apply GlobalTheory.FlatBFLoc.flatBF_of_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  first | exact @GlobalTheory.LocMod.flatFB_holds | exact GlobalTheory.LocMod.flatFB_holds | (intros; apply GlobalTheory.LocMod.flatFB_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.splitPlace_homLattice_completion_openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  intro D k _ _ _ _ p S T LS LT hLS hLT
  letI := hLS
  letI := hLT
  exact GlobalTheory.OpenCompactLat.openCompact D k p S T LS LT inferInstance inferInstance
end
