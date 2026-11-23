module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle634
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle585
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle575
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle663
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle670
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle668
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle691
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
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669

@[expose] public section

section

open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Rs.SatakeVectors PositivityTheory.Rg.Rs.SatakeVectors.SatakeVectorEventually PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JoinSatPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem satV_of_comp {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : HasSatGL w σ.ρ B) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [iSup_range_eq hV w σ h]; exact hψ
  refine ⟨?_, fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hs (fun f : MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0⟩
  obtain ⟨x, hx⟩ := hs.exists_vec
  obtain ⟨f, h0, hfV, hf⟩ := h
  haveI := σ.irred
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero
      (f.intertwiningMap_of_isIntertwiningMap σ.ρ ((finRep E N).comp (locGL E N w)) hf) with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨f x, hfV x, hx.map f hf fun e => hx.1 (hi (by rw [e, map_zero]))⟩

theorem hasSat_of_satV {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : SatV V w B) : HasSatGL w σ.ρ B := by
  obtain ⟨⟨φ, hφ, hφs⟩, -⟩ := hs
  have hfix : ∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hφs.2.1 k hk
  have hmem : φ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := by
    rw [iSup_range_eq hV w σ h]; exact hφ
  obtain ⟨v, hv0, hv⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E N).comp (locGL E N w)) σ.ρ σ.irred
    (fun f : MapsD V w σ => f.1) (fun f => f.2.2) (KGL w (n := N) : Set _) φ hφs.1 hfix hmem
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := N)) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  have e : B' = B := ((satV_of_comp hV h hB').2 φ hφ hfix hφs.1).unique hφs
  exact e ▸ hB'

theorem satV_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatV V w B) :
    SatV (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  have L := satLike_map_mulChi hχ (satLike_of_satV h)
  refine ⟨?_, L⟩
  obtain ⟨⟨φ, hφ, hs⟩, -⟩ := h
  have hm : (mulChi m χ) φ ∈ V.map (mulChi m χ).toLinearMap := Submodule.mem_map_of_mem hφ
  refine ⟨_, hm, L _ hm (fun k hk => ?_) fun e => hs.1 ((mulChi m χ).injective (by rw [e, map_zero]))⟩
  rw [finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one, one_smul]
  exact congrArg _ (GlobalTheory.LGrp.mem_fixed.1 hs.2.1 k hk)

def PartSat (w : HeightOneSpectrum (𝓞 E)) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (B : Multiset ℂˣ) : Prop :=
  SatV x.2 w B

variable {n a b : ℕ}

theorem pre_sat_iff (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    D.Sat w B ↔ ∃ l : List (Multiset ℂˣ), List.Forall₂ (PartSat w) (parts D) l ∧ l.sum = B := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨List.ofFn c, ?_, List.sum_ofFn⟩
    refine List.forall₂_iff_get.2 ⟨by simp [parts], fun i h₁ h₂ => ?_⟩
    simp only [parts, List.get_eq_getElem, List.getElem_ofFn]
    exact satV_of_comp (D.discrete _) (D.loc _ w) (hc _).2
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hlen, hg⟩ := List.forall₂_iff_get.1 hl
    have hlen' : D.c = l.length := by simpa [parts] using hlen
    have hS : ∀ i : Fin D.c, HasSatGL w (D.σ i w).ρ (l.get (i.cast hlen')) := fun i => by
      have := hg i.1 (by simp [parts]) (by simpa [hlen'] using i.2)
      simp only [parts, List.get_eq_getElem, List.getElem_ofFn] at this
      exact hasSat_of_satV (D.discrete i) (D.loc i w) this
    refine ⟨fun i => l.get (i.cast hlen'), fun i => ⟨(hS i).1, hS i⟩, ?_⟩
    have e : List.ofFn (fun i : Fin D.c => l.get (i.cast hlen')) = l :=
      List.ext_get (by simp [hlen']) fun i h₁ h₂ => by simp
    rw [← List.sum_ofFn, e]

theorem sum_map_map (f : ℂˣ → ℂˣ) (l : List (Multiset ℂˣ)) :
    (l.map (Multiset.map f)).sum = l.sum.map f := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem forall₂_tw {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {p : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l : List (Multiset ℂˣ)} (h : List.Forall₂ (PartSat w) p l) :
    List.Forall₂ (PartSat w) (p.map (twPart χ)) (l.map (Multiset.map (· * χ.val w))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons (satV_map_mulChi hχ h) ih

theorem joinSat : PositivityTheory.Rg.BcB.F.RS.JoinSat := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D w Ba Bb hJ h1 h2 sa sb
  obtain ⟨la, fa, rfl⟩ := (pre_sat_iff Pa w Ba).1 sa
  obtain ⟨lb, fb, rfl⟩ := (pre_sat_iff Pb w Bb).1 sb
  refine (pre_sat_iff D w _).2 ⟨la.map (Multiset.map (· * χ₁.val w)) ++ lb.map (Multiset.map (· * χ₂.val w)), ?_, ?_⟩
  · rw [hJ]
    exact List.rel_append (forall₂_tw h1 fa) (forall₂_tw h2 fb)
  · rw [List.sum_append, sum_map_map, sum_map_map]

end GlobalTheory.CompanionTheory.JoinSatPf

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem relIndex_ne_zero_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {V K : Subgroup H}
    (hV : IsOpen (V : Set H)) (hK : IsCompact (K : Set H)) : V.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ V.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hV.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem finH_mul (x y : Hf E a b) : finH (x * y) = finH x * finH y :=
  Prod.ext (map_mul (finGL E a) _ _) (map_mul (finGL E b) _ _)

theorem finH_one : finH (1 : Hf E a b) = 1 :=
  Prod.ext (map_one (finGL E a)) (map_one (finGL E b))

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b)
    (he₁ : ∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1), finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2))
    (he₂ : ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
      finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2))
    (i : Slot S) (G : H E a b → ℂ) (z : H E a b) :
    actS φ₁ φ₂ i G z = hint (K2 a b i.pl) fun m => sf φ₁ φ₂ i m * G (z * finH (e i m)) := by
  rcases i with w | w
  · change hint (K2 a b w.1) (fun m => φ₁ w.1 m * pairRt a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₁ w.1 m * G (z * finH (e (.inl w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₁]
    rfl
  · change hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₂ w.1 m * G (z * finH (e (.inr w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₂]
    rfl

theorem finActOf : FinActOf := by
  intro hInt hSl hConv _ E _ _ _ B S hS φ₁ φ₂ h₁ h₂ G hG l hl hfix x
  haveI := B.hν
  haveI := B.hν'
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hmul, hcont, hsep, -, hev, hmem, -⟩ := hSl E B.a B.b S hS
  obtain ⟨e, hec, hpe, hpe', he₁, he₂⟩ := GlobalTheory.T.position_embeddings_exist (E := E) B.a B.b hS
  obtain ⟨U₀, hU₀, hlev⟩ := hG
  obtain ⟨-, hc⟩ := hConv E B S hS
  obtain ⟨hcs, ⟨U₁, hU₁, hinv⟩, -⟩ := hc φ₁ φ₂ h₁ h₂
  obtain ⟨L, hLo, hLe, hLi, hLc, hLu⟩ := GlobalTheory.T.position_level_subgroups_exist (S := S) h₁ h₂
  let p : ∀ i : Slot S, Hf E B.a B.b →* GLw B.a i.pl × GLw B.b i.pl := fun i => MonoidHom.mk' (i.cp B.a B.b) (hmul i)
  let K : Subgroup (Hf E B.a B.b) := (Kf E B.a).prod (Kf E B.b)
  have hKo : IsOpen (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  have hKc : IsCompact (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf
  have hKHo : ∀ i : Slot S, IsOpen (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isOpen_K i.pl
  have hKHc : ∀ i : Slot S, IsCompact (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isCompact_K i.pl
  obtain ⟨V₀, hV₀o, hV₀K, hV₀e, hV₀U⟩ := GlobalTheory.T.restricted_product_embeddings p e K (fun i => K2 B.a B.b i.pl) hcont hec hpe hpe' hsep hmem hKc hKHo U₀ hU₀
  let V : ∀ i : Slot S, Subgroup (GLw B.a i.pl × GLw B.b i.pl) := fun i => V₀ i ⊓ L i
  have hVo : ∀ i, IsOpen (V i : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i => by
    simp only [V, Subgroup.coe_inf]
    exact (hV₀o i).inter (hLo i)
  let g : Hf E B.a B.b → ℂ := fun h => G (x * finH h)
  have hact := actS_eq φ₁ φ₂ e he₁ he₂
  have hcore := GlobalTheory.T.restricted_product_integral p e K (fun i => K2 B.a B.b i.pl) V (sf φ₁ φ₂) hpe hpe' hsep hev hmem
    (fun i => inf_le_left.trans (hV₀K i)) (fun i => relIndex_ne_zero_of_open (hVo i) (hKHc i))
    (by
      filter_upwards [hV₀e, hLe, hLu] with i a₁ a₂ a₃
      exact ⟨by simp only [V, a₁, a₂, inf_idem], a₃⟩)
    (fun i u hu y => hLi i u hu.2 y)
    (fun i => GlobalTheory.TwTrLin.finite_out_support (hVo i) (hLc i))
    g
    (fun u hu y => by
      have hu₀ : u ∈ U₀ := hV₀U u fun i => (hu i).1
      simp only [g]
      rw [finH_mul, ← mul_assoc]
      exact hlev u hu₀ _)
    l hl
    (fun i hi => funext fun y => by
      have h1 := hact i G (x * finH y)
      rw [hfix i hi] at h1
      simp only [g, finH_mul, ← mul_assoc]
      exact h1.symm)
  have hfold : ∀ (l' : List (Slot S)) (y : Hf E B.a B.b),
      l'.foldr (fun i g' x => hint (K2 B.a B.b i.pl) fun m => sf φ₁ φ₂ i m * g' (x * e i m)) g y =
        l'.foldr (fun i g' => actS φ₁ φ₂ i g') G (x * finH y) := by
    intro l'
    induction l' with
    | nil => intro y; rfl
    | cons i l' ih =>
      intro y
      simp only [List.foldr_cons]
      rw [hact]
      refine congrArg _ (funext fun m => ?_)
      rw [ih, finH_mul, mul_assoc]
  have hint₁ := hInt (Hf E B.a B.b) B.ν K (U₀ ⊓ U₁) (fun h => finFn S φ₁ φ₂ h * g h) hKo hKc
    (by rw [Subgroup.coe_inf]; exact hU₀.inter hU₁) hcs.mul_right
    (fun u hu y => by
      have e1 := (hinv u hu.2 y).2
      simp only [g]
      rw [e1, finH_mul, ← mul_assoc, hlev u hu.1])
    inferInstance
  have hF : (fun h => finFn S φ₁ φ₂ h * g h) = fun h => (∏ᶠ i : Slot S, sf φ₁ φ₂ i (p i h)) * g h :=
    funext fun h => by rw [GlobalTheory.T.finite_test_function_product h₁ h₂]; rfl
  have hfin := hfold l 1
  rw [finH_one, mul_one] at hfin
  rw [← hfin, ← hcore, ← hF]
  exact hint₁

end GlobalTheory.CompanionTheory.FinActS

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevAt

theorem aT_eq_lev (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (t : ℝ) :
    aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  apply Units.ext
  have val_emb (g : GL (Fin r) (Ad E) × GL (Fin s) (Ad E)) :
      (GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s g : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum rfl) (GlobalTheory.SmGL.stdSum rfl)
          (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    all_goals simp [GlobalTheory.CompanionTheory.CTFin.lev, GlobalTheory.SmGL.emb₂,
      GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two,
      Matrix.blockDiagonal'_apply]
  rw [PositivityTheory.Rg.Rs.JFinTr.aT_val, val_emb]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, PositivityTheory.Rg.Rs.JFinTr.aT_val, Matrix.diagonal_apply]
  have h1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  rw [h1, sub_add_cancel, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Conc.LevAt
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, iw₁, lev⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ hcm n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, iw₂, good⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact F E σ hcm n J hJ r X Y hW
  obtain ⟨K, hK, iw, -⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ hcm n J hJ r X Y hW
    K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ lev good
  exact ⟨K, hK, iw⟩
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.minimal_parabolic_rational_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | exact GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact <;> assumption)
end
