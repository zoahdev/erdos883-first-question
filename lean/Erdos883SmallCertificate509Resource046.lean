import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_46 :
    (List.ofFn coreChunks509_46).flatten =
      (coreData509.take (coreResources509 46).q).drop 90 := by
  decide +kernel

theorem coreCheck509_46 :
    ∀ c : Fin 1, (coreChunks509_46 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 46)) = true := by
  decide +kernel
#print axioms coreFlatten509_46
#print axioms coreCheck509_46
end Erdos883Verified
