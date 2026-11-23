module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
import Mathlib.Tactic.Polynomial.Basic
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004

@[expose] public section

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.Mem.ColAd.Nbhd

theorem pi_small {ι T : Type} [Finite ι] [TopologicalSpace T] (x : T) (W : Set (ι → T))
    (hW : W ∈ nhds (fun _ : ι => x)) : ∃ O ∈ nhds x, ∀ X : ι → T, (∀ i, X i ∈ O) → X ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun X hX => hsub fun i _ => Set.mem_iInter.1 (hX i) i⟩

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem exists_nsmul_intAf : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ O ∈ nhds (0 : AfE F E), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Formalism.L2.Herm.intAf F E, N • x ∈ O := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro O hO
  haveI := rlt_isModTop F E
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  have hc : Continuous (rlt_comb (F := F) b) := IsModuleTopology.continuous_of_linearMap _
  have h1 : (rlt_comb (F := F) b) ⁻¹' O ∈ nhds (0 : Fin m → FiniteAdeleRing (𝓞 F) F) :=
    hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hO)
  obtain ⟨O', hO', hsub⟩ := pi_small (0 : FiniteAdeleRing (𝓞 F) F) _ h1
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O' hO'
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨r, hr, rfl⟩ := (Set.ext_iff.1 (rlt_image_comb (F := F) b hb) x).2 hx
  rw [← map_nsmul]
  exact hsub _ fun j => hNO (r j) (hr j (Set.mem_univ _))

end Tens

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem mem_of_congOne_entry {m₀ m : ℕ} (hdvd : m₀ ∣ m) (hm : 0 < m) (x : AfE F E)
    (hx : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m : ℕ) : 𝓞 E))⁻¹ * x ∈
      Formalism.L2.Herm.intAf F E) : ∃ y ∈ Formalism.L2.Herm.intAf F E, x = m₀ • y := by
  obtain ⟨q, rfl⟩ := hdvd
  set s := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E))⁻¹ * x with hs
  have hm' : (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hm.ne'
  have hx' : x = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) * s := by
    rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hm', map_one, one_mul]
  refine ⟨(q : AfE F E) * s, mul_mem (natCast_mem _ q) hx, ?_⟩
  have hc : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) =
      ((m₀ * q : ℕ) : AfE F E) := by
    rw [map_natCast, map_natCast]
  rw [hx', hc, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

theorem congOne_nhds : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  intro F E _ _ _ _ _ n
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := rlt_isModTop F E
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)
  intro N hN
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hN
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hN
  let φ : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E) →
      Matrix (Fin n) (Fin n) (AfE F E) × (Matrix (Fin n) (Fin n) (AfE F E))ᵐᵒᵖ :=
    fun p => ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.1,
      MulOpposite.op ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.2))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_fst).prodMk (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))
  have hφ0 : φ (0, 0) = Units.embedProduct _ 1 := by
    rw [map_one]
    simp [φ]
  have h1 : φ ⁻¹' t ∈ nhds ((0, 0) : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E)) :=
    hφ.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact ht)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨u1, hu1, hu1s⟩ := pi_small (0 : Fin n → AfE F E) u hu
  obtain ⟨u2, hu2, hu2s⟩ := pi_small (0 : AfE F E) u1 hu1
  obtain ⟨v1, hv1, hv1s⟩ := pi_small (0 : Fin n → AfE F E) v hv
  obtain ⟨v2, hv2, hv2s⟩ := pi_small (0 : AfE F E) v1 hv1
  obtain ⟨m₀, hm₀, hm⟩ := exists_nsmul_intAf (F := F) (E := E) (u2 ∩ v2) (Filter.inter_mem hu2 hv2)
  refine ⟨m₀, hm₀, fun m hdvd hm0 k hk hk' => hts ?_⟩
  have ent : ∀ g : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) g → ∀ i j,
      (g : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ u2 ∩ v2 := by
    intro g hg i j
    obtain ⟨y, hy, e⟩ := mem_of_congOne_entry hdvd hm0 _ (hg i j)
    rw [e]
    exact hm y hy
  have e : Units.embedProduct _ k = φ (fun i j => (k : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j,
      fun i j => ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
    refine Prod.ext ?_ ?_
    · show (k : Matrix (Fin n) (Fin n) (AfE F E)) = _
      ext i j
      simp [φ]
    · show MulOpposite.op ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = _
      congr 1
      ext i j
      simp
  show Units.embedProduct _ k ∈ t
  rw [e]
  exact huv ⟨hu1s _ fun i => hu2s _ fun j => (ent k hk i j).1, hv1s _ fun i => hv2s _ fun j => (ent _ hk' i j).2⟩

end Main

end GlobalTheory.Mem.ColAd.Nbhd
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure AlgWtM where
  d : ℕ
  ρ : Representation ℂ (GQ L n) (Fin d → ℂ)
  alg : IsAlgWeight L n ρ
  irr : ρ.IsIrreducible

structure AutRepM extends AlgWtM L n where
  S : Submodule ℂ (GAf L n → (Fin d → ℂ))
  irrS : NG.IsIrrRep ρ S

variable {L n}

def AlgWtM.toAlgWt (m : AlgWtM L n) : NG.AlgWt L n := ⟨Fin m.d → ℂ, m.ρ, m.alg, m.irr⟩

def AutRepM.toAutRep (m : AutRepM L n) : NG.AutRep L n := ⟨m.toAlgWtM.toAlgWt, m.S, m.irrS⟩

variable (L n)

def AUq : Type := {X : Set (AutRepM L n) // ∃ π : NG.AutRep L n, X = {m | π.Iso m.toAutRep}}

def WtQ : Type := {X : Set (AlgWtM L n) // ∃ a : NG.AlgWt L n, X = {m | a.Iso m.toAlgWt}}

variable {L n}

def clsA (π : NG.AutRep L n) : AUq L n := ⟨{m | π.Iso m.toAutRep}, π, rfl⟩

def clsW (a : NG.AlgWt L n) : WtQ L n := ⟨{m | a.Iso m.toAlgWt}, a, rfl⟩

def AUq.rep (X : AUq L n) : NG.AutRep L n := X.2.choose

def WtQ.rep (X : WtQ L n) : NG.AlgWt L n := X.2.choose

theorem AUq.cls_rep (X : AUq L n) : clsA X.rep = X := Subtype.ext X.2.choose_spec.symm

theorem WtQ.cls_rep (X : WtQ L n) : clsW X.rep = X := Subtype.ext X.2.choose_spec.symm

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LocAt (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) (x : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion L)) : Prop :=
  ∃ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : s.w = w),
    IsLocS π.S s σ ∧ HEq (GlobalTheory.LocLanglands.cls σ) x

end


open Classical in
def hwOf (a : NG.AlgWt L n) (τ : L →+* ℂ) : Fin n → ℤ :=
  if h : ∃ lam, a.HWAt τ lam ∧ Antitone lam then h.choose else 0

theorem hwOf_antitone (a : NG.AlgWt L n) (τ : L →+* ℂ) : Antitone (hwOf a τ) := by
  unfold hwOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact fun _ _ _ => le_rfl


open Classical in
def satOf (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ :=
  if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAt π Dv α
  then Finset.univ.val.map h.choose_spec.choose_spec.choose else Multiset.replicate (n / 2) 1

theorem satOf_card (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset.card (satOf π w) = n / 2 := by
  unfold satOf
  split_ifs <;> simp

theorem infOf_card (lam : Fin n → ℤ) : Multiset.card (NG.infOf lam) = n := by
  simp [NG.infOf]

theorem infOf_nodup_alg {lam : Fin n → ℤ} (hl : Antitone lam) : (NG.infOf lam).Nodup ∧
    ∀ x ∈ NG.infOf lam, ∃ k : ℤ, x = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  refine ⟨?_, ?_⟩
  · unfold NG.infOf
    refine Multiset.Nodup.map_on (fun i _ j _ hij => ?_) Finset.univ.nodup
    have h1 : ((lam i - (i : ℕ) : ℤ) : ℂ) = ((lam j - (j : ℕ) : ℤ) : ℂ) := by
      push_cast; linear_combination hij
    have h2 : lam i - (i : ℕ) = lam j - (j : ℕ) := by exact_mod_cast h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hl (le_of_lt h); have : (i : ℕ) < (j : ℕ) := h; omega
    · have := hl (le_of_lt h); have : (j : ℕ) < (i : ℕ) := h; omega
  · intro x hx
    unfold NG.infOf at hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam i - (i : ℕ), by push_cast; ring⟩

end GlobalTheory.AutQuot

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

open Classical in
def wtOf (D : D7) (π : NG.AutRep D.host.E D.R.nV) : WtQ D.host.E D.R.nV :=
  if h : ∃ b, π.toAlgWt.IsDual b then clsW h.choose else clsW π.toAlgWt

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)


open Classical in
def locOf (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w


end GlobalTheory.AutQuot

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

variable {D : D7}



def twFL (L : LocAll (lay0 D)) (F : TwFrameC D) : TwFrameC (withLoc L) := { F with }


theorem twTiedL (L : LocAll (lay0 D)) {F : TwFrameC D} {low : Finset ℕ} (h : TwistFrameLowIndexCompatibility D F low) :
    TwistFrameLowIndexCompatibility (withLoc L) (twFL L F) low := { h with }


theorem choiceL (L : LocAll (lay0 D)) {C : NChoice D} (h : ChoiceC D C) : ChoiceC (withLoc L) (chL L C) := { h with }



def mtVL (L : LocAll (lay0 D)) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [g : AddCommGroup W₀]
    [m : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (V : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) : @NX.MtVReal (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ :=
  @NX.MtVReal.mk (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ V.W V.acg V.mod V.fd V.ρ V.irr V.alg V.bc V.J V.χ V.J_open V.hyp V.QP V.QP_sub V.QP_cover V.QP_nconj V.DP V.DP_sub V.DP_cover V.DP_nconj V.sp V.sp_w V.redG V.J_mem V.chi_eq V.real



def expL (L : LocAll (lay0 D)) (X : NExpTied D) : NExpTied (withLoc L) :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      (@mtVL D L i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b) (X.mtV i j b k Q ψ h1 h2 h)) }


theorem nctL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) (h : NChTie D C) : NChTie (withLoc L) (chL L C) := by
  obtain ⟨ψ0, h1, h2, -⟩ := h.psi_eq
  exact {
    twOf_eq := Sp.twOf_eq
    twSide_eq := Sp.twSide_eq
    Q_eq a := (Sp.Q_eq _ _ a ((L.X.locs_mem _ _ a).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
    psi_eq := ⟨ψ0, h1, h2, fun a g => Sp.psi_eq a g _ (h2 _ g)⟩
    embedding_baseField_condition := h.embedding_baseField_condition }


theorem chSideL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) {cf : CharFrame D} {X : NExpTied D} {tp : TupTied D cf C}
    (h : ChoiceSide D cf M X C tp) : ChoiceSide (withLoc L) (cfL L cf) (mtL L M) (expL L X) (chL L C) (tpL L tp) := by
  exact {
    nct := nctL Sp h.nct
    choice := choiceL L h.choice
    off := h.off
    adm := h.adm
    psi := h.psi
    eMt_level := h.eMt_level }




def chiDL (L : LocAll (lay0 D)) (K : NC.NChiData D) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E) : NC.NChiData (withLoc L) :=
  { K with psi := ψ }


theorem chiL (L : LocAll (lay0 D)) {K : NC.NChiData D} (h : NC.NormalizedCharacterCompatibility D K) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) :
    NC.NormalizedCharacterCompatibility (withLoc L) (chiDL L K ψ) :=
  { h with psi := hψ }


theorem deltaReadL (L : LocAll (lay0 D)) {cf : CharFrame D} (h : DeltaRead D cf) : DeltaRead (withLoc L) (cfL L cf) := h


end GlobalTheory.HeightCounting.FitTw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.OSplitBig

def sysPol (D : D7) (c : PlE D.host → ℕ → ℂ) (w : PlE D.host) : ℂ[X] :=
  X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
    C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c w k) * X ^ (D.R.nV - k)

def frobSet (D : D7) (F : Finset (PlE D.host)) : Set (G D.host.E D.nd.Om) :=
  {σ | ∃ w : PlE D.host, w ∉ F ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem dense_frobSet (D : D7) (h : GlobalTheory.RowTie.ChebSplit D.nd) (F : Finset (PlE D.host)) :
    Dense (frobSet D F) := h F

theorem heckePol_map (D : D7) (L : LocAll (lay0 D)) (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i) (v : PlE D.host)
    (hv : SplitOut (withLoc L).nd i v) :
    (heckePol (withLoc L).nd i x v).map (iotaOC (withLoc L) i) =
      sysPol D (GlobalTheory.CoefDuty.ptSys (withLoc L) i x) v := by
  have hS := hv
  obtain ⟨hsp, hl, hSi, hQ⟩ := hv
  have hgen : ∀ k ∈ Finset.Icc 1 D.R.nV,
      GenAt (withLoc L) ((withLoc L).nd.l i) ((withLoc L).nd.Q i) v k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨hsp, hl, ?_, hQ, hk1, hk2⟩
    intro hmem
    exact hSi (((withLoc L).nd.S_def i v).2 hmem)

  simp only [heckePol, sysPol, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
  Polynomial.map_mul, Polynomial.map_C]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [GlobalTheory.CoefDuty.ptSys, if_pos (hgen k hk), map_mul, map_pow, map_neg, map_one, map_natCast]
  rfl

end GlobalTheory.OSplitBig

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TwistAny

open Formalism.L2.NR

theorem exists_isRepOf_tw : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    change (cf.eta⁻¹).loc w x * (GlobalTheory.HeckeGal.Model.absPow D.host.E
      (-(D.R.t : ℝ) / 2)).loc w x = 1
    rw [hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.TwistAny
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  first | exact @GlobalTheory.Mem.Vol.volIs_trueVol | exact GlobalTheory.Mem.Vol.volIs_trueVol | (intros; apply GlobalTheory.Mem.Vol.volIs_trueVol <;> assumption)
end
