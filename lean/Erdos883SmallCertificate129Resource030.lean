import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_30 :
    (List.ofFn coreChunks129_30).flatten =
      (coreData129.take (coreResources129 30).q).drop 41 := by
  decide +kernel

theorem coreCheck129_30 :
    ∀ c : Fin 1, (coreChunks129_30 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 30)) = true := by
  decide +kernel
#print axioms coreFlatten129_30
#print axioms coreCheck129_30
end Erdos883Verified
