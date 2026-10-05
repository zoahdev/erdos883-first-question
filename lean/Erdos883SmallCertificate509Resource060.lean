import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_60 :
    (List.ofFn coreChunks509_60).flatten =
      (coreData509.take (coreResources509 60).q).drop 111 := by
  decide +kernel

theorem coreCheck509_60 :
    ∀ c : Fin 1, (coreChunks509_60 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 60)) = true := by
  decide +kernel
#print axioms coreFlatten509_60
#print axioms coreCheck509_60
end Erdos883Verified
