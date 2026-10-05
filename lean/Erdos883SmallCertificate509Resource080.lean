import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_80 :
    (List.ofFn coreChunks509_80).flatten =
      (coreData509.take (coreResources509 80).q).drop 157 := by
  decide +kernel

theorem coreCheck509_80 :
    ∀ c : Fin 1, (coreChunks509_80 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 80)) = true := by
  decide +kernel
#print axioms coreFlatten509_80
#print axioms coreCheck509_80
end Erdos883Verified
