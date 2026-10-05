import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_4 :
    (List.ofFn coreChunks83_4).flatten =
      (coreData83.take (coreResources83 4).q).drop 16 := by
  decide +kernel

theorem coreCheck83_4 :
    ∀ c : Fin 1, (coreChunks83_4 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 4)) = true := by
  decide +kernel
#print axioms coreFlatten83_4
#print axioms coreCheck83_4
end Erdos883Verified
