import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_6 :
    (List.ofFn coreChunks158_6).flatten =
      (coreData158.take (coreResources158 6).q).drop 39 := by
  decide +kernel

theorem coreCheck158_6 :
    ∀ c : Fin 1, (coreChunks158_6 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 6)) = true := by
  decide +kernel
#print axioms coreFlatten158_6
#print axioms coreCheck158_6
end Erdos883Verified
