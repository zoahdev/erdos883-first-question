import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_0 :
    (List.ofFn coreChunks83_0).flatten =
      (coreData83.take (coreResources83 0).q).drop 0 := by
  decide +kernel

theorem coreCheck83_0 :
    ∀ c : Fin 1, (coreChunks83_0 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 0)) = true := by
  decide +kernel
#print axioms coreFlatten83_0
#print axioms coreCheck83_0
end Erdos883Verified
