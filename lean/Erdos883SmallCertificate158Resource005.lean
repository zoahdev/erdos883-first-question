import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_5 :
    (List.ofFn coreChunks158_5).flatten =
      (coreData158.take (coreResources158 5).q).drop 38 := by
  decide +kernel

theorem coreCheck158_5 :
    ∀ c : Fin 1, (coreChunks158_5 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 5)) = true := by
  decide +kernel
#print axioms coreFlatten158_5
#print axioms coreCheck158_5
end Erdos883Verified
