import Erdos883AdaptiveSpan15537Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_6 : adaptiveNumericSpans15537_6.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_6 : adaptiveSpanEven15537_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_6 : adaptiveSpanEven15537_6.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_6 : adaptiveSpanEven15537_6.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_6 : adaptiveSpanWhole15537_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_6 : adaptiveSpanWhole15537_6.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_6 : adaptiveSpanWhole15537_6.spans = coreWholeSpans 0 adaptiveNumericSpans15537_6 := by
  decide +kernel
end Erdos883Verified
