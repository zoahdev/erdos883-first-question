import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_40 :
    (List.ofFn coreChunks509_40).flatten =
      (coreData509.take (coreResources509 40).q).drop 84 := by
  decide +kernel

theorem coreCheck509_40 :
    ∀ c : Fin 1, (coreChunks509_40 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 40)) = true := by
  decide +kernel
#print axioms coreFlatten509_40
#print axioms coreCheck509_40
end Erdos883Verified
