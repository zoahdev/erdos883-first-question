import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_6 :
    (List.ofFn coreChunks129_6).flatten =
      (coreData129.take (coreResources129 6).q).drop 15 := by
  decide +kernel

theorem coreCheck129_6 :
    ∀ c : Fin 1, (coreChunks129_6 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 6)) = true := by
  decide +kernel
#print axioms coreFlatten129_6
#print axioms coreCheck129_6
end Erdos883Verified
