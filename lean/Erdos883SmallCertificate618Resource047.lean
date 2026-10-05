import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_47 :
    (List.ofFn coreChunks618_47).flatten =
      (coreData618.take (coreResources618 47).q).drop 101 := by
  decide +kernel

theorem coreCheck618_47 :
    ∀ c : Fin 1, (coreChunks618_47 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 47)) = true := by
  decide +kernel
#print axioms coreFlatten618_47
#print axioms coreCheck618_47
end Erdos883Verified
