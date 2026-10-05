import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_14 :
    (List.ofFn coreChunks93_14).flatten =
      (coreData93.take (coreResources93 14).q).drop 35 := by
  decide +kernel

theorem coreCheck93_14 :
    ∀ c : Fin 1, (coreChunks93_14 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 14)) = true := by
  decide +kernel
#print axioms coreFlatten93_14
#print axioms coreCheck93_14
end Erdos883Verified
