import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_24 :
    (List.ofFn coreChunks509_24).flatten =
      (coreData509.take (coreResources509 24).q).drop 114 := by
  decide +kernel

theorem coreCheck509_24 :
    ∀ c : Fin 1, (coreChunks509_24 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 24)) = true := by
  decide +kernel
#print axioms coreFlatten509_24
#print axioms coreCheck509_24
end Erdos883Verified
