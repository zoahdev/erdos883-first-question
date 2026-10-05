import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_16 :
    (List.ofFn coreChunks129_16).flatten =
      (coreData129.take (coreResources129 16).q).drop 32 := by
  decide +kernel

theorem coreCheck129_16 :
    ∀ c : Fin 1, (coreChunks129_16 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 16)) = true := by
  decide +kernel
#print axioms coreFlatten129_16
#print axioms coreCheck129_16
end Erdos883Verified
