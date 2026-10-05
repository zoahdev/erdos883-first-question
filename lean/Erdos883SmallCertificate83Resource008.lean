import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_8 :
    (List.ofFn coreChunks83_8).flatten =
      (coreData83.take (coreResources83 8).q).drop 22 := by
  decide +kernel

theorem coreCheck83_8 :
    ∀ c : Fin 1, (coreChunks83_8 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 8)) = true := by
  decide +kernel
#print axioms coreFlatten83_8
#print axioms coreCheck83_8
end Erdos883Verified
