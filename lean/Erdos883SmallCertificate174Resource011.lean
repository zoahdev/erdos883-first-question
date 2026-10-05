import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_11 :
    (List.ofFn coreChunks174_11).flatten =
      (coreData174.take (coreResources174 11).q).drop 32 := by
  decide +kernel

theorem coreCheck174_11 :
    ∀ c : Fin 1, (coreChunks174_11 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 11)) = true := by
  decide +kernel
#print axioms coreFlatten174_11
#print axioms coreCheck174_11
end Erdos883Verified
