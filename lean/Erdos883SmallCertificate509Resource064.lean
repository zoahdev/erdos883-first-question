import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_64 :
    (List.ofFn coreChunks509_64).flatten =
      (coreData509.take (coreResources509 64).q).drop 118 := by
  decide +kernel

theorem coreCheck509_64 :
    ∀ c : Fin 1, (coreChunks509_64 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 64)) = true := by
  decide +kernel
#print axioms coreFlatten509_64
#print axioms coreCheck509_64
end Erdos883Verified
