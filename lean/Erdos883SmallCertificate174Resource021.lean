import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_21 :
    (List.ofFn coreChunks174_21).flatten =
      (coreData174.take (coreResources174 21).q).drop 48 := by
  decide +kernel

theorem coreCheck174_21 :
    ∀ c : Fin 1, (coreChunks174_21 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 21)) = true := by
  decide +kernel
#print axioms coreFlatten174_21
#print axioms coreCheck174_21
end Erdos883Verified
