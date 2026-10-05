import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_33 :
    (List.ofFn coreChunks680_33).flatten =
      (coreData680.take (coreResources680 33).q).drop 151 := by
  decide +kernel

theorem coreCheck680_33 :
    ∀ c : Fin 1, (coreChunks680_33 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 33)) = true := by
  decide +kernel
#print axioms coreFlatten680_33
#print axioms coreCheck680_33
end Erdos883Verified
