import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_4 :
    (List.ofFn coreChunks158_4).flatten =
      (coreData158.take (coreResources158 4).q).drop 36 := by
  decide +kernel

theorem coreCheck158_4 :
    ∀ c : Fin 1, (coreChunks158_4 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 4)) = true := by
  decide +kernel
#print axioms coreFlatten158_4
#print axioms coreCheck158_4
end Erdos883Verified
