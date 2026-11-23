module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle136
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle176
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle290
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MidDatum

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def mvN (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  Submodule.span (𝓞 t.X.E) ((fun (y : Fin (D.R.N i) → D.host.E) (l : Fin (D.R.N i)) => t.seam.iE.symm (y l)) ''
    (latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb : Set (Fin (D.R.N i) → D.host.E)))

def vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : HeightOneSpectrum (𝓞 D.host.F) :=
  HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P)

theorem isOver_vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : IsOver (vUnder (t := t) P) (seamP t.seam P) := by
  unfold IsOver vUnder
  rw [HeightOneSpectrum.under_asIdeal]

def vecAt {n : ℕ} (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Sp t.X.E n) : Fin n → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F :=
  fun l => prV (E := D.host.E) v (pullV (F := D.host.F) g (fun b => t.seam.iE (w b)) l)

def iotaSel (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if hι : ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1
    then hι.choose else 0

def InDom (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) : Prop :=
  vecAt (t := t) (ratA D.host.F (A.crd i hi) * x.1) (vUnder (t := t) P.1) w ∈
    latS (F := D.host.F) ((vUnder (t := t) P.1).adicCompletion D.host.F) (intV D.host.E (vUnder (t := t) P.1))
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ((St i hi).K β).lev.Lb))

def mvG (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) :
    𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ (vUnder (t := t) P.1).asIdeal then
    (if hz : InDom A i hi β x P w then
      iotaSel A i hi β P (vUnder (t := t) P.1) h (((St i hi).K β).lev.fT (vUnder (t := t) P.1) h ⟨_, hz⟩) else 0)
    else 0

end MidDatum

end GlobalTheory.TwU

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwUChiRat

open GlobalTheory.TwU Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG NumberField IsDedekindDomain

section Gen

variable {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)
  (Rel : SB → (Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) → X.K → Prop)

theorem exists_isOver (Q : HeightOneSpectrum (𝓞 D.host.E)) : ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v Q := by
  refine ⟨⟨Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, ?_⟩, rfl⟩
  intro h
  have hN : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 D.host.F) ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hN
  have : Ideal.absNorm Q.asIdeal = 0 := by exact_mod_cast hN
  exact Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)

theorem chiRatAll_of_le (hLe : LocLe s lev fb dep Rel) (hChi : ChiIs s lev fb dep Rel)
    (hK : ∀ y : X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = s.σ₀ y) : ChiRatAll lev D.what₂.embLL := by
  classical
  intro κ
  have hv : ∀ P : SB, ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP s P.1) := fun P => exists_isOver (seamP s P.1)
  choose v hv using hv
  have hU := (lev.U_eq κ.1).1 κ.2
  have hgz : ∀ P : SB, ∃ g z, Rel P g z ∧ InFrame s fb dep P κ.1 g := fun P => hLe P (v P) (hv P) κ.1 hU.1 (hU.2 (v P))
  choose g z hgz using hgz
  have h1 := hChi κ g z hgz
  obtain ⟨k, hk⟩ := hK (∏ P, z P)
  refine ⟨k⁻¹, ?_⟩
  rw [map_inv₀, hk]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end Gen

theorem chiRatAll_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ) (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), GlobalTheory.TwU.AdTie A dtU a → (∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y) → ∀ i hi β, ChiRatAll ((St i hi).K β).lev D.what₂.embLL := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ St A dtU a H hK i hi β
  have hm := m_eq t μ
  rcases Nat.lt_or_ge t.m2 i with h | h
  · rcases Nat.lt_or_ge (t.m2 + 1) i with h' | h'
    · obtain rfl : i = t.m2 + 1 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levTop β).1 (H.levTop β).2 hK
    · obtain rfl : i = t.m2 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levCpl β).1 (H.levCpl β).2.2 hK
  · have hlt : i < D.R.m := by omega
    exact chiRatAll_of_le t.seam _ _ _ _ (H.levMid i hlt h β).1 (H.levMid i hlt h β).2.2 hK

end GlobalTheory.TwUChiRat
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem not_mem_underSB_of_gIdx : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∀ v, GlobalTheory.TwU.UnderSB t μ v → ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ hQ v hv hmem
  classical
  obtain ⟨P, hP, hvP⟩ := hv
  have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P).asIdeal := by
    have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈
        (seamP t.seam P).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hvP ▸ hmem
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have h2 : ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    rw [← mem_seamP t.seam P, map_natCast]
    exact h1
  rcases Finset.mem_union.1 hP with hG | hQE
  · obtain ⟨k, hk⟩ : ∃ k, P ∈ t.Pr.vG k := by
      rcases Finset.mem_union.1 hG with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    have hgk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.pr_ok.vG_norm k P hk]
      exact Ideal.absNorm_mem P.asIdeal
    have hnd : ¬ D.what₂.places.resChar w ∣ t.Pr.g k := by
      rw [t.g_rec]
      intro hd
      exact hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hg.1 (D.host.g_prime k)).1 hd) ▸ D.host.g_level k)
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) ((t.Pr.g k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hnd)
    obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 t.X.E))
    have hone : (1 : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← hab]
      refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
      · simpa using h2
      · simpa using hgk
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  · exact hQ ((t.Q_rec μ _).2 ⟨hg.1, P, hQE, h2⟩)

end GlobalTheory.TwU
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.TwU.BaseCosetInt

theorem baseCosetRep_integral_after_scaling_at_bad_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl Kc Y cX) (t : Formalism.L2.Ker.KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ) (A : AdData t u μ St)
    (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (P : SB t μ) (l : Fin (D.R.N (t.m2 + 1))),
    IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β P l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP hA β P l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St (t.m2 + 1) (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' 1)
  have hY := hA.chain.2.1 c
  have h3 := GlobalTheory.TopInv.repY_mem t.sel (t.tup μ) (t.cst μ) _ _ hY P
  rw [← (frsF t.sel (t.tup μ) (A.pt _ (cpl_lt t μ).le c) P).apply_symm_apply (_ • _)] at h3
  replace h3 := (GlobalTheory.TopStep.frsF_mem _ P _).1 h3
  rw [map_smul] at h3
  have hint := (mem_localization_standardLattice _ _).1 h3 l
  have hmem : repY (A.yb c) ∈ A.yb c := by
    obtain ⟨y, -, hYe⟩ := hY
    exact Classical.epsilon_spec (p := fun z => z ∈ A.yb c) ⟨y, by rw [hYe]; simp⟩
  have hco := hA.coset c _ hmem P l
  rw [hc] at hco
  generalize (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) = v at hint hco
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopInv.qOf_ne P.1
  have hqi : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hint hco
  generalize (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) = e at hint ⊢
  generalize (if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M) = e0 at hco
  have key : (qOf P.1 : t.X.E) ^ e * v l = (qOf P.1 : t.X.E) ^ e * A.y0 β P l +
      (qOf P.1 : t.X.E) ^ (e + e0) * (((qOf P.1 : t.X.E) ^ e0)⁻¹ * (v l - A.y0 β P l)) := by
    rw [pow_add]
    field_simp
    ring
  rw [key] at hint
  exact (GlobalTheory.TopInv.intAt_add_iff ((hqi _).mul hco)).1 hint

end GlobalTheory.TwU.BaseCosetInt
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.TwU

theorem ratA_congAt_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (g : GL (Fin N) E), GlobalTheory.TwU.CongAt (F := F) Q n (GlobalTheory.TwU.ratA F g) → ∀ a b : Fin N, Formalism.L2.Col.IntAt Q ((((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b)) := by
  intro F E _ _ _ _ _ Q n N g h a b
  set e : E := (((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b) with he
  have hm : ((GlobalTheory.TwU.ratA F g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 =
      ((g : Matrix (Fin N) (Fin N) E) - 1).map (Formalism.L2.Col.iA F E) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have h1 := h a b
  rw [hm, Matrix.map_apply, ← map_mul] at h1
  obtain ⟨s, hs, hmem⟩ := h1
  rw [← map_mul] at hmem
  have h2 := ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).2.2.2.2 (algebraMap (𝓞 E) E s * e)).1 hmem
  obtain ⟨r, hr⟩ := h2
  exact ⟨r, s, hs, hr.symm⟩

end GlobalTheory.TwU
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

namespace GlobalTheory.TwU

theorem seamP_under_eq : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  intro D X s hs hX P Q h
  have key : ∀ a : 𝓞 D.host.F, ∃ r : 𝓞 X.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = RingOfIntegers.mapRingEquiv s.iE (algebraMap (𝓞 X.F) (𝓞 X.E) r) := by
    intro a
    set b := (RingOfIntegers.mapRingEquiv s.iE).symm (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) with hb
    have hbe : RingOfIntegers.mapRingEquiv s.iE b = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      rw [hb, RingEquiv.apply_symm_apply]
    have hfix : X.conjO b = b := by
      apply RingOfIntegers.ext
      apply s.iE.injective
      have h1 : s.iE (b : X.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) :=
        congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hbe
      have h2 : ((X.conjO b : 𝓞 X.E) : X.E) = star (b : X.E) := rfl
      rw [h2, hs.2, h1]
      have h3 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [h3, ← Formalism.BasicNotions.Examples₂.star_eq_conj]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := GlobalTheory.TwistPlaces.exists_of_conj_eq hX hfix
    exact ⟨r, by rw [hr, hbe]⟩
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
  ext a
  obtain ⟨r, hr⟩ := key a
  have hPQ : r ∈ Ideal.under (𝓞 X.F) P.asIdeal ↔ r ∈ Ideal.under (𝓞 X.F) Q.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  simp only [Ideal.under, Ideal.mem_comap] at hPQ ⊢
  rw [hr, mem_seamP, mem_seamP]
  exact hPQ

end GlobalTheory.TwU
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KerSelfDual

theorem isSDLat_latK_of_stdL : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (co : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → latCo D.sp (gramN D i hi) co a 1 lev.Lb = StandardLatticesGL3.stdL D (D.R.N i) → ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsSDLat D.host.E (D.R.N i) (latK D.sp (gramN D i hi) a x.1 lev.Lb) := by
  intro D i hi T bad lev co a hco hstd x
  have hc : IsOrthCo ((sigD D : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) :=
    GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ co hco
  have hc' : ∃ c, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) c := ⟨toLE co, hc⟩
  have hJ := GlobalTheory.isLat_dl_of_isOrthCo D.sp (gramN D i hi) hc'
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have h1 : Formalism.L2.PairingIndexBounds.F.latAd (1 : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) lev.Lb = lev.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one hLb
  have hm : mvL co (compan (sp := D.sp) (gramN D i hi) a lev.Lb) = StandardLatticesGL3.stdL D (D.R.N i) := by
    rw [← hstd, latCo, h1]
  have hsd := GlobalTheory.FourthRootStd.stdL_isSD D (D.R.N i)
  rw [← hm] at hsd
  obtain ⟨hM, hdl⟩ := GlobalTheory.OrthSelfDual.isLat_and_dl_eq_of_isSDLat_mvL D.sp (gramN D i hi) co _ hc hsd
  exact GlobalTheory.SDCompan.isSDLat_latK D.sp (gramN D i hi) hJ hc' x.1 x.2 lev.Lb a hLb hM hdl

end GlobalTheory.KerSelfDual
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧ InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  first | exact @GlobalTheory.GoodCsdTwist.exists_goodCsd_twist | exact GlobalTheory.GoodCsdTwist.exists_goodCsd_twist | (intros; apply GlobalTheory.GoodCsdTwist.exists_goodCsd_twist <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : _root_.Formalism.ConjugateSelfDual.G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  first | (exact @GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw) | (exact GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw) | (intros; apply GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

namespace GlobalTheory.Mem.Col2.KerRat

theorem rowForm_baseChange : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  intro B X I h l u a
  refine ⟨fun s hs => ?_, ?_⟩
  · exact GlobalTheory.Core.Rk.RowRead.rowEmb_linearIndependent (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a)
      (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (tilOk I h u a).2.2 B.embLL (I.perIn u a).H
      (φ := fun x : s => x.1) hs
  · have key := GlobalTheory.Core.Rk.RowRead.rowEmb_span (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a)
      (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (tilOk I h u a).2.2 B.embLL
      (GlobalTheory.Mem.FieldsLaws.fields_ok B) (φ := id) (by rw [Set.range_id, Submodule.span_univ])
    exact key

end GlobalTheory.Mem.Col2.KerRat
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.AtG

theorem ramCols_true : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  intro B X I h l Z l0 u
  have hX := (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1
  obtain ⟨κ, hκ⟩ := GlobalTheory.Core.ColZero.exists_colEquiv I h hX l u I.mu0
  have hκc : ∀ φ, κ φ = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ := fun φ => Subtype.ext (funext (hκ φ))
  have hram : ∀ φ, κ φ ∈ (I.fm l u I.mu0).ramSub ↔ φ ∈ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u := fun φ =>
    GlobalTheory.Core.ColRam.isCol_mem_ramSub_iff I h hX l u I.mu0 (κ φ) φ (hκ φ)
  have hrange : ∀ x, (I.rec7 l Z).nuIn u x ∈ (I.fm l u I.mu0).ramSub := fun x =>
    (I.rec7 l Z).nuIn_range u ▸ ⟨x, rfl⟩
  have hinj := (I.rec7 l Z).nuIn_inj u
  have hsurj : ∀ φ : Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, ∃ x, (I.rec7 l Z).nuIn u x = κ φ.1 := by
    intro φ
    have hm : κ φ.1 ∈ LinearMap.range ((I.rec7 l Z).nuIn u) := (I.rec7 l Z).nuIn_range u ▸ (hram φ.1).2 φ.2
    exact hm
  let f : ((I.rec7 l Z).div.Nu u).V → Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u := fun x =>
    ⟨κ.symm ((I.rec7 l Z).nuIn u x), (hram _).1 (Eq.subst (motive := fun y => y ∈ (I.fm l u I.mu0).ramSub) (κ.apply_symm_apply ((I.rec7 l Z).nuIn u x)).symm (hrange x))⟩
  have hf : ∀ x, κ (f x).1 = (I.rec7 l Z).nuIn u x := fun x => κ.apply_symm_apply _
  have fbij : Function.Bijective f := by
    refine ⟨fun x y e => hinj ?_, fun φ => ?_⟩
    · rw [← hf x, ← hf y, e]
    · obtain ⟨x, hx⟩ := hsurj φ
      exact ⟨x, Subtype.ext (by rw [← κ.injective.eq_iff, hf, hx])⟩
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => Subtype.ext (by
    exact (congrArg κ.symm (map_add ((I.rec7 l Z).nuIn u) x y)).trans (map_add κ.symm _ _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) fbij, ?_, ?_, ?_, ?_⟩
  · intro r x
    apply Subtype.ext
    show κ.symm _ = _
    exact (congrArg κ.symm (map_smul ((I.rec7 l Z).nuIn u) r x)).trans (map_smul κ.symm _ _)
  · intro x
    have e := GlobalTheory.Core.Ht2.colStep0_mem_lat I h hX l u I.mu0 (κ (f x).1) (f x).1 (hκ _)
    show (I.rec7 l Z).nuIn u x ∈ ((I.fm l u I.mu0).lat 0).L ↔ (f x).1 ∈ Formalism.L2.Col.MfL (Pr := B.primes X) B.wts I.Ch u
    exact (Eq.subst (motive := fun y => (y ∈ ((I.fm l u I.mu0).lat 0).L ↔ (f x).1 ∈ Formalism.L2.Col.MfL (Pr := B.primes X) B.wts I.Ch u)) (hf x) e)
  · intro x
    show _ = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (f x).1
    rw [← hκc, hf]
  · intro a φ
    funext c'
    have e := GlobalTheory.LvT.TrueStep0.rep_eCls0_symm h l u a c'
    show Formalism.L2.Col.evV _ _ _ _ (φ.1 ((I.stp u a 0).rep c').1.1.deco) =
      Formalism.L2.Col.evV _ _ _ _ (φ.1 ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco)
    rw [e]

end GlobalTheory.AtG
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

theorem _root_.GlobalTheory.T.exists_finiteCover_affineCover_of_forms_no_commonZero : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n → (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) → ∀ hg : (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F), IsFinCover ℂ X.functionField x ∧ IsAffCover p (fun i => GlobalTheory.EtProj.fOpen ι (f i)) (rB ℂ X.functionField x) ∧ ∀ j, algebraMap F X.functionField (x j) = (X.presheaf.germ (GlobalTheory.EtProj.fOpen ι (f 0)) (genericPoint X) (hg 0)).hom (GlobalTheory.EtProj.fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  first | (exact @GlobalTheory.EtProj.isFinCover_of_forms) | (exact GlobalTheory.EtProj.isFinCover_of_forms) | (intros; apply GlobalTheory.EtProj.isFinCover_of_forms  <;> assumption)
end
