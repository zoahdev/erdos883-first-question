import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_16 :
    (List.ofFn coreChunks509_16).flatten =
      (coreData509.take (coreResources509 16).q).drop 105 := by
  decide +kernel

theorem coreCheck509_16 :
    ∀ c : Fin 1, (coreChunks509_16 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 16)) = true := by
  decide +kernel
#print axioms coreFlatten509_16
#print axioms coreCheck509_16
end Erdos883Verified
