import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_37 :
    (List.ofFn coreChunks680_37).flatten =
      (coreData680.take (coreResources680 37).q).drop 157 := by
  decide +kernel

theorem coreCheck680_37 :
    ∀ c : Fin 1, (coreChunks680_37 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 37)) = true := by
  decide +kernel
#print axioms coreFlatten680_37
#print axioms coreCheck680_37
end Erdos883Verified
