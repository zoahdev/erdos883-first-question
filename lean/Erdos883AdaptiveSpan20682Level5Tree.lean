import Erdos883AdaptiveSpan20682Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_5 : adaptiveNumericSpans20682_5.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_5 : adaptiveSpanEven20682_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_5 : adaptiveSpanEven20682_5.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_5 : adaptiveSpanEven20682_5.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_5 : adaptiveSpanWhole20682_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_5 : adaptiveSpanWhole20682_5.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_5 : adaptiveSpanWhole20682_5.spans = coreWholeSpans 0 adaptiveNumericSpans20682_5 := by
  decide +kernel
end Erdos883Verified
