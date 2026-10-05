import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_7 :
    (List.ofFn coreChunks83_7).flatten =
      (coreData83.take (coreResources83 7).q).drop 20 := by
  decide +kernel

theorem coreCheck83_7 :
    ∀ c : Fin 1, (coreChunks83_7 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 7)) = true := by
  decide +kernel
#print axioms coreFlatten83_7
#print axioms coreCheck83_7
end Erdos883Verified
