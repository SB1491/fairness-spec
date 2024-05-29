From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib
     PCM IProp IPM WMM
     Mod Linking SCM Red Weakest FancyUpdate.

     From Fairness Require Import NatStructs.
Section SPEC.

  Variable ident_src: ID.
  Variable state_src: Type.

  Variable gvars : list nat.
  Variable tgt_mod : Mod.t.

  Context `{Σ: GRA.t}.
  Variable Invs : @InvSet Σ.

  Context `{MONORA: @GRA.inG monoRA Σ}.
  Context `{THDRA: @GRA.inG ThreadRA Σ}.

  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.

  Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state tgt_mod (SCMem.mod gvars))) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident tgt_mod (SCMem.mod gvars))) Σ}.

  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident tgt_mod (SCMem.mod gvars))) Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

  Context `{MEMRA: @GRA.inG memRA Σ}.

  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

(* memory_ra_alloc: *)
(*   ∀ (Σ : GRA.t) (MEMRA : GRA.inG memRA Σ) (m0 : SCMem.t) (sz : nat) (m1 : SCMem.t)  *)
(*     (p : SCMem.val), *)
(*     SCMem.alloc m0 sz = (m1, p) *)
(*     → memory_black m0 ⊢ #=> (memory_black m1 ** points_tos p (repeat (SCMem.val_nat 0) sz)) *)
  Lemma alloc_fun_spec
        sz
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        st0 (mem : SCMem.t)
    :
    ((St_tgt (st0, mem))
       -∗
       (∀ l, stsim tid E r g Q ps true itr_src (ktr_tgt l)))
      ⊢
      (stsim tid E r g Q ps pt
             itr_src
             (map_event (OMod.emb_callee tgt_mod (SCMem.mod gvars)) (SCMem.alloc_fun sz) >>= ktr_tgt)).
  Proof.
  iIntros "Q".
  unfold SCMem.alloc_fun.
  rred.
  iApply stsim_getR.
  iSplit.
  (* 
    iIntros "[ST_TGT SIM]".
    unfold SCMem.alloc_fun.
    rred. iApply stsim_getR.
    iSplit. iFrame.  rred.
  *)
  Abort.



  Lemma faa_fun_spec l v
  tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
  r g ps pt
  itr_src ktr_tgt
  st0 mem addend
  :
  (St_tgt (st0, mem))
  -∗
  (points_to l v)
  -∗
  (memory_black mem)
  -*
  (∀ m1, (St_tgt (st0, m1)) -∗ points_to l ((SCMem.val_add v addend)) -∗
  (memory_black m1)-∗ stsim tid E r g Q ps true itr_src (ktr_tgt v))
  -∗

  (stsim tid E r g Q ps pt
        itr_src
        (map_event (OMod.emb_callee tgt_mod (SCMem.mod gvars)) (SCMem.faa_fun (l, addend)) >>= ktr_tgt)).
  Proof.
    iIntros "ST_TGT POINTS_TO MEM Q".
    
    rred. iApply stsim_getR.
    iSplit. iFrame.
    rred.
    iPoseProof (memory_ra_faa with "MEM POINTS_TO") as "[% [%STORE > [i1MEM i0PTR]]]".
    erewrite STORE.
    rred. iApply (stsim_modifyR with "ST_TGT").
    iIntros "ST_TGT". ired.
    
    rred.


    iPoseProof ("Q" with "[ST_TGT]") as "Q".
    iFrame.
    iPoseProof ("Q" with "[i0PTR]") as "Q".
    iFrame.
    
    iPoseProof ("Q" with "[i1MEM]") as "Q".
    iFrame.
    iFrame.
    Qed.

  Lemma store_fun_spec 
      l v0 v1
      tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
      r g ps pt
      itr_src ktr_tgt
      st0 mem
    :
    (St_tgt (st0, mem))
    -∗
    (points_to l v0)
    -∗
    (∀m1, ( St_tgt (st0, m1)) -∗ points_to l v1 -∗
    (memory_black m1)-∗ stsim tid E r g Q ps true itr_src (ktr_tgt ()))
    -∗
    (memory_black mem)
    -*
    (stsim tid E r g Q ps pt
          itr_src
          (map_event (OMod.emb_callee tgt_mod (SCMem.mod gvars)) (SCMem.store_fun (l, v1)) >>= ktr_tgt)).
  Proof.
  iIntros "ST_TGT POINTS_TO Q MEM".
  rred. iApply stsim_getR.
  iSplit. iFrame.
  rred. 
  iPoseProof (memory_ra_store with "MEM POINTS_TO") as "[% [%STORE > [i1MEM i0PTR]]]".
  rewrite STORE. rred.    
  iApply (stsim_modifyR with "ST_TGT"). iIntros "ST_TGT". ired.
  
  
  iPoseProof ("Q" with "[ST_TGT]") as "Q". 
  iFrame.
  
  iPoseProof ("Q" with "[i0PTR]") as "Q".
  iFrame.
  
  iPoseProof ("Q" with "[i1MEM]") as "Q".
  iFrame.
  rred.
  iFrame.
Qed.
(*View value*)

  Lemma load_fun_spec
        l v
        tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
        r g ps pt
        itr_src ktr_tgt
        st0 mem
    :
    (St_tgt (st0, mem))
      -∗
      (points_to l v)
      -∗
      (St_tgt (st0, mem) -∗ points_to l v -∗
      (memory_black mem)-∗ stsim tid E r g Q ps true itr_src (ktr_tgt v))
      -∗
      (memory_black mem)
      -*
      (stsim tid E r g Q ps pt
             itr_src
             (map_event (OMod.emb_callee tgt_mod (SCMem.mod gvars)) (SCMem.load_fun l) >>= ktr_tgt)).
  Proof.
  iIntros "ST_TGT POINTS_TO Q MEM_BLACK".
  unfold SCMem.load_fun.
  rred.
  iApply stsim_getR.
  iSplit. iFrame.
  rred.
  iPoseProof (memory_ra_load with "MEM_BLACK POINTS_TO") as "[%LOAD %PERM]".
  rewrite LOAD. 
  iPoseProof ("Q" with "[ST_TGT]") as "Q".
  iFrame.
  iPoseProof ("Q" with "[POINTS_TO]") as "Q".
  iFrame.
  iPoseProof ("Q" with "[MEM_BLACK]") as "Q".
  iFrame.
  rred.
  iFrame.
  Qed.


  Lemma cas_fun_spec : True.
  Abort.

  Lemma cas_weak_fun_spec : True.
  Abort.

  Lemma compare_fun_spec : True.
  Abort.

End SPEC.
