import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_6 :
    (List.ofFn coreChunks174_6).flatten =
      (coreData174.take (coreResources174 6).q).drop 44 := by
  decide +kernel

theorem coreCheck174_6 :
    ∀ c : Fin 1, (coreChunks174_6 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 6)) = true := by
  decide +kernel
#print axioms coreFlatten174_6
#print axioms coreCheck174_6
end Erdos883Verified
