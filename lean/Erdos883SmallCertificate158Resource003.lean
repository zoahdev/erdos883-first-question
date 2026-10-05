import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_3 :
    (List.ofFn coreChunks158_3).flatten =
      (coreData158.take (coreResources158 3).q).drop 22 := by
  decide +kernel

theorem coreCheck158_3 :
    ∀ c : Fin 1, (coreChunks158_3 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 3)) = true := by
  decide +kernel
#print axioms coreFlatten158_3
#print axioms coreCheck158_3
end Erdos883Verified
