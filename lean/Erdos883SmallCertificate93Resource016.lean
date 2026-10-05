import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_16 :
    (List.ofFn coreChunks93_16).flatten =
      (coreData93.take (coreResources93 16).q).drop 41 := by
  decide +kernel

theorem coreCheck93_16 :
    ∀ c : Fin 1, (coreChunks93_16 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 16)) = true := by
  decide +kernel
#print axioms coreFlatten93_16
#print axioms coreCheck93_16
end Erdos883Verified
