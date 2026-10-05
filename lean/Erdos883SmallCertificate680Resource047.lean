import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_47 :
    (List.ofFn coreChunks680_47).flatten =
      (coreData680.take (coreResources680 47).q).drop 97 := by
  decide +kernel

theorem coreCheck680_47 :
    ∀ c : Fin 1, (coreChunks680_47 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 47)) = true := by
  decide +kernel
#print axioms coreFlatten680_47
#print axioms coreCheck680_47
end Erdos883Verified
