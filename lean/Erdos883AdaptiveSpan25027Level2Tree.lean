import Erdos883AdaptiveSpan25027Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_2 : adaptiveNumericSpans25027_2.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_2 : adaptiveSpanEven25027_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_2 : adaptiveSpanEven25027_2.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_2 : adaptiveSpanEven25027_2.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_2 : adaptiveSpanWhole25027_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_2 : adaptiveSpanWhole25027_2.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_2 : adaptiveSpanWhole25027_2.spans = coreWholeSpans 0 adaptiveNumericSpans25027_2 := by
  decide +kernel
end Erdos883Verified
