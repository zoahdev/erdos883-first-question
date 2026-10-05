import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_9 :
    (List.ofFn coreChunks158_9).flatten =
      (coreData158.take (coreResources158 9).q).drop 19 := by
  decide +kernel

theorem coreCheck158_9 :
    ∀ c : Fin 1, (coreChunks158_9 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 9)) = true := by
  decide +kernel
#print axioms coreFlatten158_9
#print axioms coreCheck158_9
end Erdos883Verified
